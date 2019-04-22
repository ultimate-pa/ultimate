/*
 * Copyright (C) 2019 Luca Bruder (luca.bruder@gmx.de)
 *
 * This file is part of the ULTIMATE Library-ModelCheckerUtils library.
 *
 * The ULTIMATE Library-ModelCheckerUtils library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by the Free Software Foundation,
 * either version 3 of the License, or (at your option) any later version.
 *
 * The ULTIMATE Library-ModelCheckerUtils library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-ModelCheckerUtils library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-ModelCheckerUtils library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-ModelCheckerUtils library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.mapelim.monniaux;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.IdentityTransformer;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain.FormulaToEqDisjunctiveConstraintConverter.StoreChainSquisher;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Luca Bruder (luca.bruder@gmx.de)
 * @author Lisa Kleinlein (lisa.kleinlein@web.de)
 */
public class MonniauxMapEliminator implements IIcfgTransformer<IcfgLocation> {

	private final ManagedScript mMgdScript;
	private final IIcfg<IcfgLocation> mIcfg;
	private final IIcfg<IcfgLocation> mResultIcfg;
	private final ILogger mLogger;
	private final IBacktranslationTracker mBacktranslationTracker;
	private final int mCells;

	public MonniauxMapEliminator(final ILogger logger, final IIcfg<IcfgLocation> icfg,
			final IBacktranslationTracker backtranslationTracker, final int cells) {
		mIcfg = Objects.requireNonNull(icfg);
		mMgdScript = Objects.requireNonNull(mIcfg.getCfgSmtToolkit().getManagedScript());
		mLogger = logger;
		mBacktranslationTracker = backtranslationTracker;
		// mCells = cells;
		// TODO: Change value of mCells back, when testing is finished
		mCells = 1;
		mResultIcfg = eliminateMaps();
	}

	@Override
	public IIcfg<IcfgLocation> getResult() {
		return mResultIcfg;
	}

	private IIcfg<IcfgLocation> eliminateMaps() {

		final BasicIcfg<IcfgLocation> resultIcfg =
				new BasicIcfg<>(mIcfg.getIdentifier() + "ME", mIcfg.getCfgSmtToolkit(), IcfgLocation.class);
		final ILocationFactory<IcfgLocation, IcfgLocation> funLocFac = (oldLocation, debugIdentifier, procedure) -> {
			final IcfgLocation rtr = new IcfgLocation(debugIdentifier, procedure);
			ModelUtils.copyAnnotations(oldLocation, rtr);
			return rtr;
		};

		final TransformedIcfgBuilder<IcfgLocation, IcfgLocation> lst = new TransformedIcfgBuilder<>(mLogger, funLocFac,
				mBacktranslationTracker, new IdentityTransformer(mIcfg.getCfgSmtToolkit()), mIcfg, resultIcfg);
		mMgdScript.lock(this);
		iterate(lst);
		lst.finish();
		mMgdScript.unlock(this);
		return resultIcfg;
	}

	private void iterate(final TransformedIcfgBuilder<IcfgLocation, IcfgLocation> lst) {

		final Script script = mMgdScript.getScript();

		// Create mappings from original ProgramVars to a set of mCells new ProgramVars
		final IIcfgSymbolTable symboltable = mIcfg.getCfgSmtToolkit().getSymbolTable();
		final Set<IProgramNonOldVar> globals = symboltable.getGlobals();
		final Set<ILocalProgramVar> locals = new HashSet<>();
		for (final Entry<String, IcfgLocation> entry : mIcfg.getProcedureEntryNodes().entrySet()) {
			final String proc = entry.getKey();
			final Set<ILocalProgramVar> someLocals = symboltable.getLocals(proc);
			locals.addAll(someLocals);
		}

		final Set<IProgramVar> programArrayVars = new HashSet<>(globals.size() + locals.size());
		globals.stream().filter(a -> a.getSort().isArraySort()).forEach(programArrayVars::add);
		locals.stream().filter(a -> a.getSort().isArraySort()).forEach(programArrayVars::add);

		// Fill the sets idxD and valD with a certain number (mCells) of new program variables for each program
		// variable of the sort array
		final Map<IProgramVar, Set<IProgramVar>> idxVars = new LinkedHashMap<>();
		final Map<IProgramVar, Set<IProgramVar>> valVars = new LinkedHashMap<>();
		for (final IProgramVar var : programArrayVars) {
			assert var.getSort().isArraySort();
			assert var.getSort().getArguments().length == 2 : "Array sort with != 2 arguments";
			final Sort indexSort = var.getSort().getArguments()[0];
			final Sort valueSort = var.getSort().getArguments()[1];

			final Set<IProgramVar> idx = new LinkedHashSet<>();
			final Set<IProgramVar> val = new LinkedHashSet<>();
			for (int i = 0; i < mCells; i++) {
				final String idxName = (var.toString() + "_idx_" + Integer.toString(i));
				final String valName = (var.toString() + "_val_" + Integer.toString(i));

				final IProgramVar varIdx =
						ProgramVarUtils.constructGlobalProgramVarPair(idxName, indexSort, mMgdScript, this);
				final IProgramVar varVal =
						ProgramVarUtils.constructGlobalProgramVarPair(valName, valueSort, mMgdScript, this);
				idx.add(varIdx);
				val.add(varVal);
			}
			idxVars.put(var, idx);
			valVars.put(var, val);
		}

		final Map<IProgramVar, Set<Term>> idxAssignments = new LinkedHashMap<>();

		final IcfgEdgeIterator iter = new IcfgEdgeIterator(mIcfg);
		while (iter.hasNext()) {
			final IIcfgTransition<?> transition = iter.next();
			// Iterate over relevant edges
			if (transition instanceof IIcfgInternalTransition) {

				final IIcfgInternalTransition<?> internalTransition = (IIcfgInternalTransition<?>) transition;
				final UnmodifiableTransFormula tf = internalTransition.getTransformula();

				final Term tfTerm = tf.getFormula();

				final StoreChainSquisher scs = new StoreChainSquisher(mMgdScript);
				final Term atMostOneStore = scs.transform(tfTerm);
				final Collection<Term> arrayEqualities = scs.getReplacementEquations();
				final Collection<Term> newAuxVars = scs.getReplacementTermVariables();

				final StoreSelectEqualityCollector ssec = new StoreSelectEqualityCollector();
				ssec.transform(atMostOneStore);

				if (ssec.isEmpty()) {
					final IcfgLocation oldSource = internalTransition.getSource();
					final IcfgLocation newSource = lst.createNewLocation(oldSource);
					final IcfgLocation oldTarget = internalTransition.getTarget();
					final IcfgLocation newTarget = lst.createNewLocation(oldTarget);
					lst.createNewInternalTransition(newSource, newTarget, tf, false);
					continue;
				}

				final Map<Term, Term> subst = new HashMap<>();

				// Create new in- out- and auxVars, if necessary
				final Set<TermVariable> auxVars = new HashSet<>(tf.getAuxVars());
				for (final TermVariable aux : auxVars) {
					if (aux.getSort().isArraySort()) {
						throw new UnsupportedOperationException("Arrays in auxVariables");
					}
				}
				for (final Term var : newAuxVars) {
					auxVars.add((TermVariable) var);
				}

				final Map<IProgramVar, TermVariable> newInVars = new HashMap<>(tf.getInVars());
				final Map<IProgramVar, TermVariable> newOutVars = new HashMap<>(tf.getOutVars());

				final Map<Term, Set<Term>> hierarchy = new LinkedHashMap<>();
				final Map<Term, Set<Term>> idxTerms = new LinkedHashMap<>();
				final Map<Term, IProgramVar> oldTermToProgramVar = new LinkedHashMap<>();
				final Map<Term, IProgramVar> idxTermToIdxProgramVar = new LinkedHashMap<>();
				for (final IProgramVar arrayVar : programArrayVars) {

					final TermVariable arrayInTermVar = newInVars.remove(arrayVar);
					final TermVariable arrayOutTermVar = newOutVars.remove(arrayVar);
					// In- and OutVars for indices
					final Set<Term> idxTermVarSet = new LinkedHashSet<>();
					for (final IProgramVar idxVar : idxVars.get(arrayVar)) {
						final TermVariable idxTermVar =
								mMgdScript.constructFreshTermVariable((idxVar.toString() + "_term"), idxVar.getSort());

						/*
						 * if (idxAssignments.containsKey(idxVar)) { for (final Term temp : idxAssignments.get(idxVar))
						 * { final IProgramVar req = reqVars.get(temp); if (newInVars.containsKey(req)) {
						 * newInVars.remove(req); } newInVars.put(req, ((TermVariable) temp)); } }
						 */

						if (idxAssignments.containsKey(idxVar)) {
							for (final Term term : idxAssignments.get(idxVar)) {
								newInVars.put(idxVar, ((TermVariable) term));
							}
						}
						newOutVars.put(idxVar, idxTermVar);
						idxTermToIdxProgramVar.put(idxTermVar, idxVar);
						idxTermVarSet.add(idxTermVar);
					}
					if (arrayInTermVar != null) {
						idxTerms.put(arrayInTermVar, idxTermVarSet);
					}
					if (arrayOutTermVar != null) {
						idxTerms.put(arrayOutTermVar, idxTermVarSet);
					}

					// InVars for values

					if (arrayInTermVar != null) {
						final Set<Term> valTermVars = new LinkedHashSet<>();
						for (final IProgramVar valVar : valVars.get(arrayVar)) {
							final TermVariable valTermVar = mMgdScript
									.constructFreshTermVariable((valVar.toString() + "_in"), valVar.getSort());
							newInVars.put(valVar, valTermVar);
							valTermVars.add(valTermVar);
						}
						hierarchy.put(arrayInTermVar, valTermVars);

						// Checking if the scs added new variables which need
						// to be added to the hierarchy
						for (final Term aterm : arrayEqualities) {
							if (aterm instanceof ApplicationTerm) {
								final Term params[] = ((ApplicationTerm) aterm).getParameters();
								final Term store = params[0];
								final Term storeParams[] = ((ApplicationTerm) store).getParameters();
								final Term storeVar = storeParams[0];
								if (storeVar == arrayInTermVar) {
									hierarchy.put(params[1], valTermVars);
									idxTerms.put(params[1], idxTerms.get(arrayInTermVar));
								}
							}
						}
					}

					// OutVars for values

					if (arrayOutTermVar != null) {
						final Set<Term> valTermVars = new LinkedHashSet<>();
						for (final IProgramVar valVar : valVars.get(arrayVar)) {
							final TermVariable valTermVar;
							if (ssec.hasNoStoEqu()) {
								valTermVar = newInVars.get(valVar);
							} else {
								valTermVar = mMgdScript
										.constructFreshTermVariable((valVar.toString() + "_out"), valVar.getSort());
							}
							newOutVars.put(valVar, valTermVar);
							valTermVars.add(valTermVar);
							oldTermToProgramVar.put(valTermVar, valVar);
						}
						hierarchy.put(arrayOutTermVar, valTermVars);

						// Checking if the scs added new variables which need
						// to be added to the hierarchy
						for (final Term aterm : arrayEqualities) {
							if (aterm instanceof ApplicationTerm) {
								final Term params[] = ((ApplicationTerm) aterm).getParameters();
								final Term store = params[0];
								final Term storeParams[] = ((ApplicationTerm) store).getParameters();
								final Term storeVar = storeParams[0];
								if (storeVar == arrayInTermVar) {
									hierarchy.put(params[1], valTermVars);
									idxTerms.put(params[1], idxTerms.get(arrayOutTermVar));
								}
							}
						}
					}
				}

				final Set<Term> addendum = new LinkedHashSet<>();
				// Eliminate the Select-, Store-, and Equality-Terms
				for (final Term selectTerm : ssec.mSelectTerms) {
					final ApplicationTerm aSelectTerm = (ApplicationTerm) selectTerm;
					final Pair<TermVariable, Term> substTerm = eliminateSelects(mMgdScript, idxTerms, aSelectTerm,
							hierarchy, auxVars, subst, idxTermToIdxProgramVar, idxAssignments, newInVars);
					subst.put(selectTerm, substTerm.getFirst());
					addendum.add(substTerm.getSecond());

				}
				for (final Term storeTerm : ssec.mStoreTerms) {
					final ApplicationTerm aStoreTerm = (ApplicationTerm) storeTerm;
					final Term substTerm = eliminateStores(mMgdScript, idxTerms, aStoreTerm, hierarchy, newInVars,
							oldTermToProgramVar, subst, newAuxVars, idxTermToIdxProgramVar, idxAssignments);
					subst.put(storeTerm, substTerm);
				}
				for (final Term equalityTerm : ssec.mEqualityTerms) {
					final ApplicationTerm aEqualityTerm = (ApplicationTerm) equalityTerm;
					final Term substTerm = eliminateEqualities(mMgdScript, idxTerms, aEqualityTerm, hierarchy, subst);
					subst.put(equalityTerm, substTerm);
				}

				final Set<Term> constraints = new HashSet<>();
				for (final IProgramVar var : programArrayVars) {
					for (final IProgramVar idxVar : idxVars.get(var)) {
						final Set<Term> equalities = new HashSet<>();
						if (!idxAssignments.containsKey(idxVar)) {
							continue;
						}
						for (final Term con : idxAssignments.get(idxVar)) {
							equalities.add(SmtUtils.binaryEquality(script, newOutVars.get(idxVar), con));
						}
						constraints.add(SmtUtils.or(script, equalities));
					}
				}

				addendum.add(SmtUtils.and(script, constraints));
				addendum.add(atMostOneStore);

				final Term newTfTerm = new SubstitutionWithLocalSimplification(mMgdScript, subst)
						.transform(SmtUtils.and(script, addendum));
				final UnmodifiableTransFormula newTf =
						buildTransitionFormula(tf, newTfTerm, newInVars, newOutVars, auxVars);

				final IcfgLocation oldSource = internalTransition.getSource();
				final IcfgLocation newSource = lst.createNewLocation(oldSource);
				final IcfgLocation oldTarget = internalTransition.getTarget();
				final IcfgLocation newTarget = lst.createNewLocation(oldTarget);
				final IcfgInternalTransition newTransition =
						lst.createNewInternalTransition(newSource, newTarget, newTf, true);
				mLogger.info(newSource);
				mLogger.info("In  " + tf.toStringDirect());
				mLogger.info("Out " + newTf.toStringDirect());
				mLogger.info(newTarget);

				for (final IProgramVar dsa : programArrayVars) {
					for (final IProgramVar idxVar : idxVars.get(dsa)) {
						if (idxAssignments.containsKey(idxVar)) {
							idxAssignments.remove(idxVar);
							final Set<Term> newCons = new HashSet<>();
							newCons.add((newOutVars.get(idxVar)));
							idxAssignments.put(idxVar, newCons);
						}
					}
				}

				mBacktranslationTracker.rememberRelation(internalTransition, newTransition);

			} else {
				throw new UnsupportedOperationException("Not yet implemented");
			}
		}
	}

	private UnmodifiableTransFormula buildTransitionFormula(final UnmodifiableTransFormula oldFormula,
			final Term newTfFormula, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars, final Collection<TermVariable> auxVars) {
		final Set<IProgramConst> nonTheoryConsts = oldFormula.getNonTheoryConsts();
		final boolean emptyAuxVars = auxVars.isEmpty();
		final Collection<TermVariable> branchEncoders = oldFormula.getBranchEncoders();
		final boolean emptyBranchEncoders = branchEncoders.isEmpty();
		final boolean emptyNonTheoryConsts = nonTheoryConsts.isEmpty();
		final TransFormulaBuilder tfb = new TransFormulaBuilder(inVars, outVars, emptyNonTheoryConsts, nonTheoryConsts,
				emptyBranchEncoders, branchEncoders, emptyAuxVars);

		tfb.setFormula(newTfFormula);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		auxVars.stream().forEach(tfb::addAuxVar);

		mMgdScript.unlock(this);
		final UnmodifiableTransFormula utf = tfb.finishConstruction(mMgdScript);
		mMgdScript.lock(this);
		return utf;
	}

	private static Pair<TermVariable, Term> eliminateSelects(final ManagedScript mMgdScript,
			final Map<Term, Set<Term>> idxTerms, final ApplicationTerm selectTerm, final Map<Term, Set<Term>> hierarchy,
			final Set<TermVariable> auxVars, final Map<Term, Term> subst,
			final Map<Term, IProgramVar> idxTermToIdxProgramVar, final Map<IProgramVar, Set<Term>> idxAssignments,
			final Map<IProgramVar, TermVariable> newInVars) {
		// Find the parameters of the ApplicationTerm and check if they have already been substituted
		final Term[] params = selectTerm.getParameters();
		final Term x;
		final Term y;
		// TODO: Is this check relevant?
		if (subst.containsKey(params[0])) {
			x = subst.get(params[0]);
		} else {
			x = params[0];
		}
		if (subst.containsKey(params[1])) {
			y = subst.get(params[1]);
		} else {
			y = params[1];
		}

		final Script script = mMgdScript.getScript();

		final Sort sort = x.getSort().getArguments()[1];
		final TermVariable placeholder = mMgdScript.constructFreshTermVariable((x.toString() + "_aux"), sort);
		auxVars.add(placeholder);
		Term substTerm;
		final Set<Term> implications = new HashSet<>();
		for (final Term val : hierarchy.get(params[0])) {
			for (final Term idx : idxTerms.get(params[0])) {
				final Set<Term> tempAssignments = new HashSet<>();
				if (idxAssignments.containsKey(idxTermToIdxProgramVar.get(idx))) {
					for (final Term asgn : idxAssignments.get(idxTermToIdxProgramVar.get(idx))) {
						tempAssignments.add(asgn);
					}
				}
				tempAssignments.add(y);
				idxAssignments.put(idxTermToIdxProgramVar.get(idx), tempAssignments);
				implications.add(SmtUtils.implies(script, SmtUtils.binaryEquality(script, y, idx),
						SmtUtils.binaryEquality(script, val, placeholder)));
			}
		}

		substTerm = SmtUtils.and(script, implications);

		final Pair<TermVariable, Term> auxTerm = new Pair<>(placeholder, substTerm);
		return auxTerm;
	}

	private static Term eliminateStores(final ManagedScript mMgdScript, final Map<Term, Set<Term>> idxTerms,
			final ApplicationTerm storeTerm, final Map<Term, Set<Term>> hierarchy,
			final Map<IProgramVar, TermVariable> newInVars, final Map<Term, IProgramVar> oldTermToProgramVar,
			final Map<Term, Term> subst, final Collection<Term> newAuxVars,
			final Map<Term, IProgramVar> idxTermToIdxProgramVar, final Map<IProgramVar, Set<Term>> idxAssignments) {
		// Find the parameters of the ApplicationTerm and check if they have already been substituted

		final Term[] paramsTerm = storeTerm.getParameters();
		Term x = paramsTerm[0];
		Term y = paramsTerm[0];
		Term z = paramsTerm[0];
		for (int i = 0; i < paramsTerm.length; ++i) {
			final Term param = paramsTerm[i];
			if (param instanceof ApplicationTerm) {
				final Term[] paramsStore = ((ApplicationTerm) param).getParameters();
				x = paramsStore[0];
				y = paramsStore[1];
				z = paramsStore[2];
			}
		}

		final Script script = mMgdScript.getScript();

		final Set<Term> rtr = new LinkedHashSet<>();
		for (final Term val : hierarchy.get(x)) {
			final Term valLow;
			if (newInVars.containsValue(val) || newAuxVars.contains(x)) {
				valLow = val;
			} else {
				valLow = newInVars.get(oldTermToProgramVar.get(x));
			}

			for (final Term idx : idxTerms.get(x)) {
				final Set<Term> tempAssignments = new HashSet<>();
				if (idxAssignments.containsKey(idxTermToIdxProgramVar.get(idx))) {
					for (final Term asgn : idxAssignments.get(idxTermToIdxProgramVar.get(idx))) {
						tempAssignments.add(asgn);
					}
				}
				tempAssignments.add(y);
				idxAssignments.put(idxTermToIdxProgramVar.get(idx), tempAssignments);

				rtr.add(SmtUtils.implies(script, SmtUtils.binaryEquality(script, y, idx),
						SmtUtils.binaryEquality(script, val, z)));
				rtr.add(SmtUtils.implies(script, SmtUtils.distinct(script, idx, y),
						SmtUtils.binaryEquality(script, val, valLow)));
			}
		}
		return SmtUtils.and(script, rtr);
	}

	private static Term eliminateEqualities(final ManagedScript mMgdScript, final Map<Term, Set<Term>> idxTerms,
			final ApplicationTerm equalityTerm, final Map<Term, Set<Term>> hierarchy, final Map<Term, Term> subst) {
		final Term[] params = equalityTerm.getParameters();

		if (!(params[0] instanceof TermVariable)) {
			return equalityTerm;
		}
		if (!(params[1] instanceof TermVariable)) {
			return equalityTerm;
		}

		// Find the parameters of the ApplicationTerm and check if they have already been substituted
		final Term x;
		final Term y;
		if (subst.containsKey(params[0])) {
			x = subst.get(params[0]);
		} else {
			x = params[0];
		}
		if (subst.containsKey(params[1])) {
			y = subst.get(params[1]);
		} else {
			y = params[1];
		}

		final Script script = mMgdScript.getScript();

		final Set<Term> rtr = new LinkedHashSet<>();
		final Set<Term> xvals = hierarchy.get(params[0]);
		for (final Term xval : xvals) {
			final Set<Term> xidxs = idxTerms.get(params[0]);
			for (final Term xidx : xidxs) {
				for (final Term yval : hierarchy.get(params[1])) {
					for (final Term yidx : idxTerms.get(params[1])) {
						rtr.add(SmtUtils.implies(script, SmtUtils.binaryEquality(script, xidx, yidx),
								SmtUtils.binaryEquality(script, xval, yval)));
					}
				}
			}
		}
		return SmtUtils.and(script, rtr);
	}

}
