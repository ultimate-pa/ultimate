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

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.IdentityTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.FormulaToEqDisjunctiveConstraintConverter.StoreChainSquisher;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Luca Bruder (luca.bruder@gmx.de)
 */
public class MonniauxMapEliminator implements IIcfgTransformer<IcfgLocation> {

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;
	private final IIcfg<IcfgLocation> mIcfg;
	private final IIcfg<IcfgLocation> mResultIcfg;
	private final ILogger mLogger;
	private final IBacktranslationTracker mBacktranslationTracker;
	private final int mCells;

	public MonniauxMapEliminator(final IUltimateServiceProvider services, final ILogger logger,
			final IIcfg<IcfgLocation> icfg, final IBacktranslationTracker backtranslationTracker, final int cells) {
		mServices = services;
		mIcfg = Objects.requireNonNull(icfg);
		mMgdScript = Objects.requireNonNull(mIcfg.getCfgSmtToolkit().getManagedScript());
		mLogger = logger;
		mBacktranslationTracker = backtranslationTracker;
		mCells = cells;
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
		final Map<IProgramVar, List<IProgramVar>> valVars = new LinkedHashMap<>();
		final Set<IProgramVar> allPrgValVars = new LinkedHashSet<>();
		for (final IProgramVar var : programArrayVars) {
			assert var.getSort().isArraySort();
			assert var.getSort().getArguments().length == 2 : "Array sort with != 2 arguments";
			final Sort indexSort = var.getSort().getArguments()[0];
			final Sort valueSort = var.getSort().getArguments()[1];

			final Set<IProgramVar> idx = new LinkedHashSet<>();
			final List<IProgramVar> val = new ArrayList<>();
			for (int i = 0; i < mCells; i++) {
				final String idxName = (var.toString() + "_idx_" + Integer.toString(i));
				final String valName = (var.toString() + "_val_" + Integer.toString(i));

				final IProgramVar varIdx =
						ProgramVarUtils.constructGlobalProgramVarPair(SmtUtils.removeSmtQuoteCharacters(idxName), indexSort, mMgdScript, this);
				final IProgramVar varVal =
						ProgramVarUtils.constructGlobalProgramVarPair(SmtUtils.removeSmtQuoteCharacters(valName), valueSort, mMgdScript, this);
				idx.add(varIdx);
				val.add(varVal);
				allPrgValVars.add(varVal);
			}
			idxVars.put(var, idx);
			valVars.put(var, val);
		}

		final Map<IProgramVar, Pair<Term, IProgramVar>> bools = new LinkedHashMap<>();
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

				final Term atMostOneStore = SmtUtils.toDnf(
						mServices, mMgdScript, scs.transform(tfTerm), XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
				//final Term atMostOneStore = scs.transform(tfTerm);
				final Collection<Term> arrayEqualities = scs.getReplacementEquations();
				final Collection<Term> newAuxVars = scs.getReplacementTermVariables();

				final StoreSelectEqualityCollector ssec = new StoreSelectEqualityCollector();
				ssec.transform(atMostOneStore);
				Boolean iterate = ssec.hasMultDim();

				if (ssec.isEmpty()) {
					final IcfgLocation oldSource = internalTransition.getSource();
					final IcfgLocation newSource = lst.createNewLocation(oldSource);
					final IcfgLocation oldTarget = internalTransition.getTarget();
					final IcfgLocation newTarget = lst.createNewLocation(oldTarget);
					lst.createNewTransition(newSource, newTarget, (IcfgEdge) internalTransition);
					continue;
				}

				final Map<Term, Term> subst = new HashMap<>();

				// Create new in- out- and auxVars, if necessary
				final Set<TermVariable> auxVars = new HashSet<>(tf.getAuxVars());
				for (final Term var : newAuxVars) {
					auxVars.add((TermVariable) var);
				}

				final Map<Term, Set<Term>> idxAuxVars = new LinkedHashMap<>();
				final Map<Term, List<Term>> valAuxVars = new LinkedHashMap<>();
				final Set<Term> tempAux = new LinkedHashSet<>();
				for (final TermVariable var : auxVars) {
					assert var.getSort().isArraySort();
					assert var.getSort().getArguments().length == 2 : "Array sort with != 2 arguments";
					if (!var.getSort().isArraySort()) {
						continue;
					}
					final Sort indexSort = var.getSort().getArguments()[0];
					final Sort valueSort = var.getSort().getArguments()[1];

					final Set<Term> idx = new LinkedHashSet<>();
					final List<Term> val = new ArrayList<>();
					
					for (int i = 0; i < mCells; i++) {
						final String idxName = (var.toString() + "_idx_" + Integer.toString(i));
						final String valName = (var.toString() + "_val_" + Integer.toString(i));

						final TermVariable varIdx = mMgdScript.constructFreshTermVariable(
								SmtUtils.removeSmtQuoteCharacters(idxName), indexSort);

						final TermVariable varVal = mMgdScript.constructFreshTermVariable(
								SmtUtils.removeSmtQuoteCharacters(valName), valueSort);
						idx.add(varIdx);
						val.add(varVal);
						tempAux.add(varIdx);
						tempAux.add(varVal);
						
					}
					idxAuxVars.put(var, idx);
					valAuxVars.put(var, val);
				}
				for (final Term aux : tempAux) {
					auxVars.add(((TermVariable) aux));
				}

				/*
				 * for (final TermVariable aux : auxVars) { if (aux.getSort().isArraySort()) { throw new
				 * UnsupportedOperationException("Arrays in auxVariables"); } }
				 */

				final Map<IProgramVar, TermVariable> newInVars = new HashMap<>(tf.getInVars());
				final Map<IProgramVar, TermVariable> newOutVars = new HashMap<>(tf.getOutVars());

				final Map<Term, List<Term>> hierarchy = new LinkedHashMap<>();
				final Map<Term, Set<Term>> idxTerms = new LinkedHashMap<>();
				final Map<Term, IProgramVar> oldTermToProgramVar = new LinkedHashMap<>();
				final Map<Term, IProgramVar> idxTermToIdxProgramVar = new LinkedHashMap<>();
				final Set<IProgramVar> oldProgramVars = new LinkedHashSet<>();
				for (final IProgramVar var : newInVars.keySet()) {
					oldProgramVars.add(var);
				}
				for (final IProgramVar var : newOutVars.keySet()) {
					oldProgramVars.add(var);
				}
				final Map<IProgramVar, List<TermVariable>> oldProgramVarsToOutVars = new LinkedHashMap<>();
				final Map<IProgramVar, List<TermVariable>> oldProgramVarsToInVars = new LinkedHashMap<>();

				for (final IProgramVar arrayVar : programArrayVars) {

					final TermVariable arrayInTermVar = newInVars.remove(arrayVar);
					final TermVariable arrayOutTermVar = newOutVars.remove(arrayVar);
					// TODO: Maybe delete later
					/*
					 * TermVariable arrayAuxTermVar = null; for (TermVariable termVar : auxVars) { if
					 * (termVar.toString().contains(arrayVar.toString())) { arrayAuxTermVar = termVar; } }
					 */

					// In- and OutVars for indices
					final Set<Term> idxTermVarSet = new LinkedHashSet<>();
					for (final IProgramVar idxVar : idxVars.get(arrayVar)) {
						final TermVariable idxTermVar =
								mMgdScript.constructFreshTermVariable(
										SmtUtils.removeSmtQuoteCharacters(idxVar.toString() + "_term"),
										idxVar.getSort());

						/*if (idxAssignments.containsKey(idxVar)) {
							for (final Term term : idxAssignments.get(idxVar)) {
								newInVars.put(idxVar, ((TermVariable) term));
							}
						}*/
						
						if (!bools.containsKey(idxVar)) {
							final TermVariable idxBool = mMgdScript.constructFreshTermVariable(
									SmtUtils.removeSmtQuoteCharacters(
											(idxVar.toString() + "_term") + "_assigned"),SmtSortUtils.getBoolSort(script));
							final IProgramVar boolPrg =
									ProgramVarUtils.constructGlobalProgramVarPair(
											SmtUtils.removeSmtQuoteCharacters(idxVar.toString() + "_bool"),
											SmtSortUtils.getBoolSort(script), mMgdScript, this);
							bools.put(idxVar, new Pair<>(idxBool, boolPrg));
						}
						
						newInVars.put(idxVar, idxTermVar);
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
					// TODO: Maybe delete later
					/*
					 * if (arrayAuxTermVar != null) { auxVars.remove(arrayAuxTermVar); idxTerms.put(arrayAuxTermVar,
					 * idxTermVarSet); }
					 */
					
					// In- and OutVars for bools
					for (final IProgramVar idx : bools.keySet()) {
						final IProgramVar boolPrg = bools.get(idx).getSecond();
						final Term boolTerm = bools.get(idx).getFirst();
						newInVars.put(boolPrg, ((TermVariable) boolTerm));
						newOutVars.put(boolPrg, ((TermVariable) boolTerm));
					}

					// InVars for values

					if (arrayInTermVar != null) {
						final List<Term> valTermVars = new ArrayList<>();
						final List<TermVariable> valTermVars2 = new ArrayList<>();
						for (final IProgramVar valVar : valVars.get(arrayVar)) {
							final TermVariable valTermVar = mMgdScript
									.constructFreshTermVariable(SmtUtils.removeSmtQuoteCharacters(valVar.toString() + "_in"), valVar.getSort());
							newInVars.put(valVar, valTermVar);
							valTermVars.add(valTermVar);
							valTermVars2.add(valTermVar);
						}
						hierarchy.put(arrayInTermVar, valTermVars);
						oldProgramVarsToInVars.put(arrayVar, valTermVars2);

						// Checking if the scs added new variables which need
						// to be added to the hierarchy
						for (final Term aterm : arrayEqualities) {
							if (aterm instanceof ApplicationTerm) {
								final Term params[] = ((ApplicationTerm) aterm).getParameters();
								final Term store;
								if (params[0] instanceof ApplicationTerm) {
									store = params[0];
								}
								else {
									store = params[1];
								}
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
						final List<Term> valTermVars = new ArrayList<>();
						final List<TermVariable> valTermVars2 = new ArrayList<>();
						for (final IProgramVar valVar : valVars.get(arrayVar)) {
							final TermVariable valTermVar;
							if (ssec.hasNoStoEqu()) {
								valTermVar = newInVars.get(valVar);
							} else {
								valTermVar = mMgdScript.constructFreshTermVariable(
										SmtUtils.removeSmtQuoteCharacters(valVar.toString() + "_out"), valVar.getSort());
								// valTermVar = newInVars.get(valVar);
							}
							newOutVars.put(valVar, valTermVar);
							valTermVars.add(valTermVar);
							valTermVars2.add(valTermVar);
							oldTermToProgramVar.put(valTermVar, valVar);
						}
						hierarchy.put(arrayOutTermVar, valTermVars);
						oldProgramVarsToOutVars.put(arrayVar, valTermVars2);

						// Checking if the scs added new variables which need
						// to be added to the hierarchy
						for (final Term aterm : arrayEqualities) {
							if (aterm instanceof ApplicationTerm) {
								final Term params[] = ((ApplicationTerm) aterm).getParameters();
								final ApplicationTerm store;
								if (params[0] instanceof ApplicationTerm) {
									store = ((ApplicationTerm) params[0]);
								} else {
									store = ((ApplicationTerm) params[1]);
								}
								final Term storeParams[] = store.getParameters();
								final Term storeVar = storeParams[0];
								if (storeVar == arrayInTermVar) {
									hierarchy.put(params[1], valTermVars);
									idxTerms.put(params[1], idxTerms.get(arrayOutTermVar));
								}
							}
						}
					}
				}

				final Map<Term, Term> iterImp = new LinkedHashMap<>();
				final Set<Term> addendum = new LinkedHashSet<>();
				final Map<IProgramVar, Pair<List<Term>, Integer>> chain = new LinkedHashMap<>();
				final Map<Term, Term> lowValues = new LinkedHashMap<>();
				// Eliminate the Select-, Store-, and Equality-Terms
				for (final Term selectTerm : ssec.mSelectTerms) {
					final ApplicationTerm aSelectTerm = (ApplicationTerm) selectTerm;
					final Pair<TermVariable, Term> substTerm = eliminateSelects(mMgdScript, idxTerms, aSelectTerm,
							hierarchy, auxVars, subst, idxTermToIdxProgramVar, idxAssignments, newInVars, chain,
							oldProgramVars, mCells, valVars, lowValues, idxAuxVars, valAuxVars, iterImp);
					subst.put(selectTerm, substTerm.getFirst());
					addendum.add(substTerm.getSecond());

				}
				for (final Term storeTerm : ssec.mStoreTerms) {
					final ApplicationTerm aStoreTerm = (ApplicationTerm) storeTerm;
					final Term substTerm = eliminateStores(mMgdScript, idxTerms, aStoreTerm, hierarchy, newInVars,
							oldTermToProgramVar, subst, newAuxVars, idxTermToIdxProgramVar, idxAssignments, chain,
							mCells, valVars, lowValues, oldProgramVars, idxAuxVars, valAuxVars);
					subst.put(storeTerm, substTerm);
				}
				for (final Term equalityTerm : ssec.mEqualityTerms) {
					final ApplicationTerm aEqualityTerm = (ApplicationTerm) equalityTerm;
					final Term substTerm = eliminateEqualities(mMgdScript, idxTerms, aEqualityTerm, hierarchy, subst);
					subst.put(equalityTerm, substTerm);
				}

				
				for (final IProgramVar key : newInVars.keySet()) {
					if (allPrgValVars.contains(key)) {
						addendum.add(SmtUtils.binaryEquality(script, newInVars.get(key), newOutVars.get(key)));
					}
				}
				
				final Map<Integer, Set<Pair<Term, Set<Term>>>> disAssgn = new HashMap<>();
				final Map<Term, Term> newSubst = new HashMap<>();
				final Term[] disjuncts = SmtUtils.getDisjuncts(atMostOneStore);
				for (int i = 0; i < disjuncts.length; i++) {
					final Term term = disjuncts[i];
					final StoreSelectEqualityCollector newSsec = new StoreSelectEqualityCollector();
					newSsec.transform(term);
					final Set<Term> ors = new HashSet<>();
					final Set<Term> storeTerms = new HashSet<>(newSsec.mStoreTerms);
					for (final Term storeTerm : storeTerms) {
						final ApplicationTerm aStoreTerm = ((ApplicationTerm) storeTerm);
						final Term[] paramsTerm = aStoreTerm.getParameters();
						Term x = paramsTerm[0];
						Term y = paramsTerm[0];
						for (int j = 0; j < paramsTerm.length; j++) {
							final Term param = paramsTerm[j];
							if (param instanceof ApplicationTerm) {
								final Term[] paramsStore = ((ApplicationTerm) param).getParameters();
								x = paramsStore[0];
								y = paramsStore[1];
							}
						}
						
						Set<Term> idxs = idxTerms.get(x);
						if (idxs != null) {
							
						} else {
							idxs = idxAuxVars.get(x);
						}
						
						for (final Term idx : idxs) {
							final Set<Pair<Term, Set<Term>>> wholeSet;
							if (disAssgn.get(i) != null) {
								wholeSet = new HashSet<>(disAssgn.get(i));
							} else {
								wholeSet = null;
							}
							if (wholeSet != null) {
								for (Pair<Term, Set<Term>> pairAssgn : wholeSet) {
									final Set<Term> assgn = new HashSet<>(pairAssgn.getSecond());
									assgn.add(y);
									final Set<Pair<Term, Set<Term>>> tempSet = new HashSet<>(wholeSet);
									tempSet.add(new Pair<>(idx, assgn));
									disAssgn.put(i, tempSet);
									// TODO: Find the correct way to implement a "verum"
									if (!auxVars.contains(idx)) {
										ors.add(bools.get(idxTermToIdxProgramVar.get(idx)).getFirst());
									}
								}	
							} else {
								final Set<Term> assgn = new HashSet<>();
								assgn.add(y);
								final Set<Pair<Term, Set<Term>>> tempSet = new HashSet<>();
								tempSet.add(new Pair<>(idx, assgn));
								disAssgn.put(i, tempSet);
								// TODO: Find the correct way to implement a "verum"
								if (!auxVars.contains(idx)) {
									ors.add(bools.get(idxTermToIdxProgramVar.get(idx)).getFirst());
								}
							}
							
						}
					}
					
					final Set<Term> selectTerms = new HashSet<>(newSsec.mSelectTerms);
					for (final Term selectTerm : selectTerms) {
						final ApplicationTerm aSelectTerm = ((ApplicationTerm) selectTerm);
						final Term[] paramsTerm = aSelectTerm.getParameters();
						Term x = paramsTerm[0];
						Term y = paramsTerm[1];
						Set<Term> idxs = idxTerms.get(x);
						if (idxs != null) {
							
						} else {
							idxs = idxAuxVars.get(x);
						}
						
						for (final Term idx : idxs) {
							final Set<Pair<Term, Set<Term>>> wholeSet;
							if (disAssgn.get(i) != null) {
								wholeSet = new HashSet<>(disAssgn.get(i));
							} else {
								wholeSet = null;
							}
							if (wholeSet != null) {
								for (Pair<Term, Set<Term>> pairAssgn : wholeSet) {
									final Set<Term> assgn = pairAssgn.getSecond();
									assgn.add(y);
									final Set<Pair<Term, Set<Term>>> tempSet = new HashSet<>(wholeSet);
									tempSet.add(new Pair<>(idx, assgn));
									disAssgn.put(i, tempSet);
									// TODO: Find the correct way to implement a "true"
									if (!auxVars.contains(idx)) {
										ors.add(bools.get(idxTermToIdxProgramVar.get(idx)).getFirst());
									}
								}	
							} else {
								final Set<Term> assgn = new HashSet<>();
								assgn.add(y);
								final Set<Pair<Term, Set<Term>>> tempSet = new HashSet<>();
								tempSet.add(new Pair<>(idx, assgn));
								disAssgn.put(i, tempSet);
								// TODO: Find the correct way to implement a "true"
								if (!auxVars.contains(idx)) {
									ors.add(bools.get(idxTermToIdxProgramVar.get(idx)).getFirst());
								}
							}	
						}
					}
					
					if (disAssgn.get(i) != null) {
						for (final Pair<Term, Set<Term>> pair : disAssgn.get(i)) {
							final Set<Term> assignments = pair.getSecond();
							final Term idx = pair.getFirst();
							final Set<Term> equalities = new HashSet<>();
							for (final Term assgn : assignments) {
								equalities.add(SmtUtils.binaryEquality(script, idx, assgn));
							}
							final IProgramVar idxPrgVar = idxTermToIdxProgramVar.get(idx);
							if (idxPrgVar != null) {
								ors.add(SmtUtils.implies(
										script, bools.get(idxTermToIdxProgramVar.get(idx)).getFirst(), SmtUtils.or(script, equalities)));
							}
						}
					}
					
					ors.add(term);
					newSubst.put(term, SmtUtils.and(script, ors));
				}
				
				
				final Term tempTfTerm = new SubstitutionWithLocalSimplification(mMgdScript, newSubst)
						.transform(atMostOneStore);
				
				addendum.add(tempTfTerm);
				
				final Term newTfTerm = new SubstitutionWithLocalSimplification(mMgdScript, subst)
						.transform(SmtUtils.and(script, addendum));
				
				Term finalTfTerm = newTfTerm;
				
				while (iterate) {
					//TODO
					final Term iterDnf = SmtUtils.toDnf(
							mServices, mMgdScript, scs.transform(newTfTerm), XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
					final StoreSelectEqualityCollector iterSsec = new StoreSelectEqualityCollector();
					iterSsec.transform(iterDnf);
					
					final Map<Term, Term> iterSubst = new HashMap<>();
					final Set<Term> iterAdd = new LinkedHashSet<>();
					for (final Term selectTerm : iterSsec.mSelectTerms) {
						final ApplicationTerm aSelectTerm = (ApplicationTerm) selectTerm;
						final Pair<TermVariable, Term> substTerm = eliminateSelects(mMgdScript, idxTerms, aSelectTerm,
								hierarchy, auxVars, subst, idxTermToIdxProgramVar, idxAssignments, newInVars, chain,
								oldProgramVars, mCells, valVars, lowValues, idxAuxVars, valAuxVars, iterImp);
						iterSubst.put(selectTerm, substTerm.getFirst());
						iterAdd.add(substTerm.getSecond());

					}
					
					
					
					
					
					
					
					
					
					
					
					
					
					for (final IProgramVar key : newInVars.keySet()) {
						if (allPrgValVars.contains(key)) {
							iterAdd.add(SmtUtils.binaryEquality(script, newInVars.get(key), newOutVars.get(key)));
						}
					}
					
					final Map<Integer, Set<Pair<Term, Set<Term>>>> disAssgn2 = new HashMap<>();
					final Map<Term, Term> newSubst2 = new HashMap<>();
					final Term[] disjuncts2 = SmtUtils.getDisjuncts(iterDnf);
					for (int i = 0; i < disjuncts2.length; i++) {
						final Term term = disjuncts2[i];
						final StoreSelectEqualityCollector newSsec = new StoreSelectEqualityCollector();
						newSsec.transform(term);
						final Set<Term> ors = new HashSet<>();
						
						final Set<Term> selectTerms = new HashSet<>(newSsec.mSelectTerms);
						for (final Term selectTerm : selectTerms) {
							final ApplicationTerm aSelectTerm = ((ApplicationTerm) selectTerm);
							final Term[] paramsTerm = aSelectTerm.getParameters();
							Term x = paramsTerm[0];
							Term y = paramsTerm[1];
							Set<Term> idxs = idxTerms.get(x);
							if (idxs != null) {
								
							} else {
								idxs = idxAuxVars.get(x);
							}
							
							for (final Term idx : idxs) {
								final Set<Pair<Term, Set<Term>>> wholeSet;
								if (disAssgn2.get(i) != null) {
									wholeSet = new HashSet<>(disAssgn2.get(i));
								} else {
									wholeSet = null;
								}
								if (wholeSet != null) {
									for (Pair<Term, Set<Term>> pairAssgn : wholeSet) {
										final Set<Term> assgn = pairAssgn.getSecond();
										assgn.add(y);
										final Set<Pair<Term, Set<Term>>> tempSet = new HashSet<>(wholeSet);
										tempSet.add(new Pair<>(idx, assgn));
										disAssgn2.put(i, tempSet);
										// TODO: Find the correct way to implement a "true"
										if (!auxVars.contains(idx)) {
											ors.add(bools.get(idxTermToIdxProgramVar.get(idx)).getFirst());
										}
									}	
								} else {
									final Set<Term> assgn = new HashSet<>();
									assgn.add(y);
									final Set<Pair<Term, Set<Term>>> tempSet = new HashSet<>();
									tempSet.add(new Pair<>(idx, assgn));
									disAssgn2.put(i, tempSet);
									// TODO: Find the correct way to implement a "true"
									if (!auxVars.contains(idx)) {
										ors.add(bools.get(idxTermToIdxProgramVar.get(idx)).getFirst());
									}
								}	
							}
						}
						
						if (disAssgn2.get(i) != null) {
							for (final Pair<Term, Set<Term>> pair : disAssgn2.get(i)) {
								final Set<Term> assignments = pair.getSecond();
								final Term idx = pair.getFirst();
								final Set<Term> equalities = new HashSet<>();
								for (final Term assgn : assignments) {
									equalities.add(SmtUtils.binaryEquality(script, idx, assgn));
								}
								final IProgramVar idxPrgVar = idxTermToIdxProgramVar.get(idx);
								if (idxPrgVar != null) {
									ors.add(SmtUtils.implies(
											script, bools.get(idxTermToIdxProgramVar.get(idx)).getFirst(), SmtUtils.or(script, equalities)));
								} else {
									ors.add(SmtUtils.or(script, equalities));
								}
							}
						}
						
						ors.add(term);
						newSubst2.put(term, SmtUtils.and(script, ors));
					}
					
					
					final Term tempTfTerm2 = new SubstitutionWithLocalSimplification(mMgdScript, newSubst2)
							.transform(iterDnf);
					
					iterAdd.add(tempTfTerm2);
					
					finalTfTerm = new SubstitutionWithLocalSimplification(mMgdScript, iterSubst)
							.transform(SmtUtils.and(script, iterAdd));
					
					
					
					
					
					
					
					
					
					
					
					
					
					
					
					
					
					
					
					
					
					
					iterate = iterSsec.hasMultDim();
				}
				
				final UnmodifiableTransFormula newTf =
						buildTransitionFormula(tf, finalTfTerm, newInVars, newOutVars, auxVars);

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
			final Map<Term, Set<Term>> idxTerms, final ApplicationTerm selectTerm,
			final Map<Term, List<Term>> hierarchy, final Set<TermVariable> auxVars, final Map<Term, Term> subst,
			final Map<Term, IProgramVar> idxTermToIdxProgramVar, final Map<IProgramVar, Set<Term>> idxAssignments,
			final Map<IProgramVar, TermVariable> newInVars, final Map<IProgramVar, Pair<List<Term>, Integer>> chain,
			final Set<IProgramVar> oldProgramVars, final int mCells, final Map<IProgramVar, List<IProgramVar>> valVars,
			final Map<Term, Term> lowValues, final Map<Term, Set<Term>> idxAuxVars,
			final Map<Term, List<Term>> valAuxVars, final Map<Term, Term> iterImp) {
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


		final List<Term> vals = new ArrayList<>();
		final List<Term> idxs = new ArrayList<>();
		IProgramVar old = null;
		for (final IProgramVar var : oldProgramVars) {
			if (x.toString().contains(var.toString())) {
				old = var;
			}
		}
		
		if (hierarchy.containsKey(x)) {
			for (final Term val : hierarchy.get(x)) {
				vals.add(val);
			}
			for (final Term idx : idxTerms.get(x)) {
				idxs.add(idx);
			}
		}
		if (!hierarchy.containsKey(x) && !chain.containsKey(old) && !auxVars.contains(x)) {
			for (int i = 0; i < mCells; i++) {
				final String valName = (old.toString() + "_val_" + Integer.toString(i) + Integer.toString(0));
				final Term varVal =
						mMgdScript.constructFreshTermVariable(SmtUtils.removeSmtQuoteCharacters(valName),
								valVars.get(old).iterator().next().getSort());
				vals.add(varVal);
			}
			chain.put(old, new Pair<>(vals, 0));
			for (final Term idx : idxTerms.get(newInVars.get(old))) {
				idxs.add(idx);
			}
		}
		if (chain.containsKey(old)) {
			final int length = chain.get(old).getValue() + 1;
			for (int i = 0; i < mCells; i++) {
				final String valName = (old.toString() + "_val_" + Integer.toString(i) + Integer.toString(length));
				final Term varVal =
						mMgdScript.constructFreshTermVariable(SmtUtils.removeSmtQuoteCharacters(valName),
								valVars.get(old).iterator().next().getSort());
				vals.add(varVal);
				lowValues.put(varVal, chain.get(old).getFirst().get(length - 1));
			}
			chain.remove(old);
			chain.put(old, new Pair<>(vals, length));
			for (final Term idx : idxTerms.get(newInVars.get(old))) {
				idxs.add(idx);
			}
		}
		if (valAuxVars.containsKey(x)) {
			for (final Term val : valAuxVars.get(x)) {
				vals.add(val);
			}
			for (final Term idx : idxAuxVars.get(x)) {
				idxs.add(idx);
			}
		}
		
		final Script script = mMgdScript.getScript();
		// If we are iterating since we found multidimensional arrays we need to create new term variables for the earlier created aux variables
		if (vals.isEmpty() && idxs.isEmpty()) {
			final Set<Term> idx2 = new LinkedHashSet<>();
			final List<Term> val2 = new ArrayList<>();
			for (int i = 0; i < mCells; ++i) {
				assert x.getSort().isArraySort();
				assert x.getSort().getArguments().length == 2 : "Array sort with != 2 arguments";
				if (!x.getSort().isArraySort()) {
					continue;
				}
				final Sort indexSort = y.getSort();
				final Sort valueSort = x.getSort();
				
				final String idxName = (x.toString() + "_iterIdx" + Integer.toString(i));
				final String valName = (x.toString() + "_iterVal" + Integer.toString(i));

				final TermVariable varIdx = mMgdScript.constructFreshTermVariable(
							SmtUtils.removeSmtQuoteCharacters(idxName), indexSort);

				final TermVariable varVal = mMgdScript.constructFreshTermVariable(
							SmtUtils.removeSmtQuoteCharacters(valName), valueSort);
				idx2.add(varIdx);
				val2.add(varVal);
				idxs.add(varIdx);
				vals.add(varVal);
				auxVars.add(varVal);
				auxVars.add(varIdx);
				
			}
			idxAuxVars.put(x, idx2);
			valAuxVars.put(x, val2);
		}

		if (iterImp.containsKey(x)) {
			final Sort sort = x.getSort().getArguments()[1];
			final TermVariable placeholder = mMgdScript.constructFreshTermVariable(SmtUtils.removeSmtQuoteCharacters(x.toString() + "_aux"), sort);
			auxVars.add(placeholder);
			Term substTerm;
			final Set<Term> implications = new HashSet<>();
			for (final Term val : vals) {
				for (final Term idx : idxs) {
					final Set<Term> tempAssignments = new HashSet<>();
					if (idxAssignments.containsKey(idxTermToIdxProgramVar.get(idx))) {
						for (final Term asgn : idxAssignments.get(idxTermToIdxProgramVar.get(idx))) {
							tempAssignments.add(asgn);
						}
					}
					tempAssignments.add(y);
					idxAssignments.put(idxTermToIdxProgramVar.get(idx), tempAssignments);
					implications.add(SmtUtils.implies(script, SmtUtils.and(script, SmtUtils.binaryEquality(script, y, idx), iterImp.get(x)),
							SmtUtils.binaryEquality(script, val, x)));
					iterImp.put(val, SmtUtils.binaryEquality(script, y, idx));
				}
			}

			substTerm = SmtUtils.and(script, implications);

			final Pair<TermVariable, Term> auxTerm = new Pair<>(placeholder, substTerm);
			return auxTerm;
		}

		final Sort sort = x.getSort().getArguments()[1];
		final TermVariable placeholder = mMgdScript.constructFreshTermVariable(SmtUtils.removeSmtQuoteCharacters(x.toString() + "_aux"), sort);
		auxVars.add(placeholder);
		Term substTerm;
		final Set<Term> implications = new HashSet<>();
		for (final Term val : vals) {
			for (final Term idx : idxs) {
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
				iterImp.put(placeholder, SmtUtils.binaryEquality(script, y, idx));
			}
		}

		substTerm = SmtUtils.and(script, implications);

		final Pair<TermVariable, Term> auxTerm = new Pair<>(placeholder, substTerm);
		return auxTerm;
	}

	private static Term eliminateStores(final ManagedScript mMgdScript, final Map<Term, Set<Term>> idxTerms,
			final ApplicationTerm storeTerm, final Map<Term, List<Term>> hierarchy,
			final Map<IProgramVar, TermVariable> newInVars, final Map<Term, IProgramVar> oldTermToProgramVar,
			final Map<Term, Term> subst, final Collection<Term> newAuxVars,
			final Map<Term, IProgramVar> idxTermToIdxProgramVar, final Map<IProgramVar, Set<Term>> idxAssignments,
			final Map<IProgramVar, Pair<List<Term>, Integer>> chain, final int mCells,
			final Map<IProgramVar, List<IProgramVar>> valVars, final Map<Term, Term> lowValues,
			final Set<IProgramVar> oldProgramVars, final Map<Term, Set<Term>> idxAuxVars,
			final Map<Term, List<Term>> valAuxVars) {
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

		final List<Term> vals = new ArrayList<>();
		final List<Term> idxs = new ArrayList<>();
		IProgramVar old = null;
		for (final IProgramVar var : oldProgramVars) {
			if (x.toString().contains(var.toString())) {
				old = var;
			}
		}
		if (hierarchy.containsKey(x)) {
			for (final Term val : hierarchy.get(x)) {
				vals.add(val);
			}
			for (final Term idx : idxTerms.get(x)) {
				idxs.add(idx);
			}
		}
		if (!hierarchy.containsKey(x) && !chain.containsKey(old) && !valAuxVars.containsKey(x)) {
			for (int i = 0; i < mCells; i++) {
				final String valName = (old.toString() + "_val_" + Integer.toString(i) + Integer.toString(0));
				final Term varVal =
						mMgdScript.constructFreshTermVariable(SmtUtils.removeSmtQuoteCharacters(valName),
								valVars.get(old).iterator().next().getSort());
				vals.add(varVal);
			}
			chain.put(old, new Pair<>(vals, 0));
			for (final Term idx : idxTerms.get(newInVars.get(old))) {
				idxs.add(idx);
			}
		}
		if (chain.containsKey(old)) {
			final int length = chain.get(old).getValue() + 1;
			for (int i = 0; i < mCells; i++) {
				final String valName = (old.toString() + "_val_" + Integer.toString(i) + Integer.toString(length));
				final Term varVal =
						mMgdScript.constructFreshTermVariable(SmtUtils.removeSmtQuoteCharacters(valName),
								valVars.get(old).iterator().next().getSort());
				vals.add(varVal);
				lowValues.put(varVal, chain.get(old).getFirst().get(length - 1));
			}
			chain.remove(old);
			chain.put(old, new Pair<>(vals, length));
			for (final Term idx : idxTerms.get(newInVars.get(old))) {
				idxs.add(idx);
			}
		}
		if (valAuxVars.containsKey(x)) {
			for (final Term val : valAuxVars.get(x)) {
				vals.add(val);
			}
			for (final Term idx : idxAuxVars.get(x)) {
				idxs.add(idx);
			}
		}

		final Script script = mMgdScript.getScript();

		final Set<Term> rtr = new LinkedHashSet<>();
		for (final Term val : vals) {
			final Term valLow;
			if (newInVars.containsValue(val) || newAuxVars.contains(x)) {
				valLow = val;
			} else {
				if (chain.containsKey(old)) {
					valLow = lowValues.get(val);
				} else {
					valLow = newInVars.get(oldTermToProgramVar.get(x));
				}

			}

			for (final Term idx : idxs) {
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
			final ApplicationTerm equalityTerm, final Map<Term, List<Term>> hierarchy, final Map<Term, Term> subst) {
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
		final List<Term> xvals = hierarchy.get(params[0]);
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
