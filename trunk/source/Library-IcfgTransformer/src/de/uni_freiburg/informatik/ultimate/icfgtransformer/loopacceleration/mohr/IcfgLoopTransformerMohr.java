/*
 * Copyright (C) 2017 Moritz Mohr (mohrm@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.mohr;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.IdentityTransformer;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Dnf;

public class IcfgLoopTransformerMohr<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private final IIcfg<OUTLOC> mResult;
	private final TransformedIcfgBuilder<INLOC, OUTLOC> mTib;
	private final ManagedScript mManagedScript;
	private final IIcfgSymbolTable mSymbolTable;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	public IcfgLoopTransformerMohr(final ILogger logger, final IUltimateServiceProvider services,
			final IIcfg<INLOC> originalIcfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker, final Class<OUTLOC> outLocationClass,
			final String newIcfgIdentifier) {

		// Notes:
		// you can use SimultaneousUpdate and TransformulaUtils.computeGuard to decompose transformulas in their update
		// and guard parts
		// use the TransFormulaBuilder tfb = new TransFormulaBuilder(inVars, outVars, emptyNonTheoryConsts,
		// nonTheoryConsts, emptyBranchEncoders, branchEncoders, emptyAuxVars);
		// new Overapprox("Because of loop acceleration", null).annotate(edge)
		// use mTib to create the new IIcfg

		mManagedScript = originalIcfg.getCfgSmtToolkit().getManagedScript();
		mServices = services;
		mLogger = logger;
		mSymbolTable = originalIcfg.getCfgSmtToolkit().getSymbolTable();
		final BasicIcfg<OUTLOC> resultIcfg =
				new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(), outLocationClass);
		final IdentityTransformer identityTransformer = new IdentityTransformer(mSymbolTable);
		mTib = new TransformedIcfgBuilder<>(funLocFac, backtranslationTracker, identityTransformer, originalIcfg,
				resultIcfg);
		mResult = transform(originalIcfg);
		mTib.finish();
	}

	private IIcfg<OUTLOC> transform(final IIcfg<INLOC> origIcfg) {
		final IcfgLoopDetection<INLOC> loopDetector = new IcfgLoopDetection<>(origIcfg);
		final Set<IcfgLoop<INLOC>> loops = loopDetector.getResult();
		for (final IcfgLoop<INLOC> loop : loops) {
			@SuppressWarnings("unused")
			final UnmodifiableTransFormula loopSummaryTransformula = transformLoop(loop);
		}

		return null;
	}

	private UnmodifiableTransFormula transformLoop(final IcfgLoop<INLOC> loop) {
		final ArrayList<Map<IProgramVar, Term>> symbolicMem = new ArrayList<>();
		final Set<IProgramVar> assignedVariables = new HashSet<>();
		final Set<TermVariable> assignedKappas = new HashSet<>();
		final ArrayList<TermVariable> kappas = new ArrayList<>();
		final Map<Term, Term> kappaTauRel = new HashMap<>();
		final Set<Term> kappaTerms = new HashSet<>();
		final Set<ArrayList<IcfgEdge>> paths = loop.getPaths();
		final ArrayList<Set<Term>> pathAssertions = new ArrayList<>();
		int pathCount = 0;
		for (final ArrayList<IcfgEdge> p : paths) {
			pathAssertions.add(new HashSet<>());
			symbolicMem.add(new HashMap<>());
			final TermVariable kappa = mManagedScript.constructFreshTermVariable("kappa" + pathCount,
					mManagedScript.getScript().sort("Int"));
			kappas.add(kappa);
			kappaTauRel.put(kappa, mManagedScript.constructFreshTermVariable("tau" + pathCount,
					mManagedScript.getScript().sort("Int")));
			for (final IcfgEdge edge : p) {
				final TransFormula formula = edge.getTransformula();
				final Term term = formula.getFormula();
				if (!formula.getAssignedVars().isEmpty() && term instanceof ApplicationTerm) {
					final ApplicationTerm appTerm = (ApplicationTerm) term;
					final IProgramVar progVar = formula.getAssignedVars().iterator().next();
					final Term assignedTerm = appTerm.getParameters()[1];
					assignedVariables.add(progVar);
					updateSymbolicMemory(cleanVariables(assignedTerm, formula.getInVars()), kappa,
							formula.getAssignedVars().iterator().next(), symbolicMem.get(pathCount),
							formula.getInVars(), assignedKappas, kappaTerms);
				} else {
					pathAssertions.get(pathCount).add(cleanVariables(term, formula.getInVars()));
				}
			}
			pathCount++;
		}

		final Map<Term, Term> summarizedSymbMemory = new HashMap<>();
		for (final IProgramVar variable : assignedVariables) {
			final ArrayList<Term> pathSums = new ArrayList<>();
			for (final Map<IProgramVar, Term> pathSM : symbolicMem) {
				final Term smTerm = pathSM.get(variable);
				if (smTerm instanceof ApplicationTerm
						&& kappaTerms.contains(((ApplicationTerm) smTerm).getParameters()[1])) {
					pathSums.add(((ApplicationTerm) smTerm).getParameters()[1]);
				} else if (smTerm != null) {
					pathSums.clear();
					break;
				}
			}
			if (!pathSums.isEmpty()) {
				final Term[] parameters = new Term[pathSums.size() + 1];
				pathSums.toArray(parameters);
				parameters[pathSums.size()] = variable.getTermVariable();
				final Term t = mManagedScript.getScript().term("+", parameters);
				summarizedSymbMemory.put(variable.getTermVariable(), t);
				continue;
			}
			Term constant = null;
			final Set<TermVariable> k = new HashSet<>();
			pathCount = 0;
			for (final Map<IProgramVar, Term> pathSM : symbolicMem) {
				final Term smTerm = pathSM.get(variable);
				pathCount++;
				if (smTerm instanceof ConstantTerm) {
					if (constant != null) {
						if (!smTerm.equals(constant)) {
							constant = null;
							break;
						}
					} else {
						constant = smTerm;
					}
					k.add(kappas.get(pathCount));
				} else if (smTerm instanceof TermVariable
						&& assignedVariables.contains(mSymbolTable.getProgramVar((TermVariable) smTerm))) {
					if (constant != null) {
						if (!smTerm.equals(constant)) {
							constant = null;
							break;
						}
					} else {
						constant = smTerm;
					}
					k.add(kappas.get(pathCount));
				} else if (smTerm instanceof ApplicationTerm) {
					final TermVariable[] freeTVs = smTerm.getFreeVars();
					for (final TermVariable tv : freeTVs) {
						if (assignedVariables.contains(mSymbolTable.getProgramVar(tv))) {
							constant = null;
							break;
						}
					}
					if (constant != null) {
						if (!smTerm.equals(constant)) {
							constant = null;
							break;
						}
					} else {
						constant = smTerm;
					}
					k.add(kappas.get(pathCount));
				}
			}
			if (constant != null) {
				final Term[] ks = new Term[k.size()];
				k.toArray(ks);
				final Term sum = mManagedScript.getScript().term("+", ks);
				final Term cond = mManagedScript.getScript().term("<",
						Rational.ZERO.toTerm(mManagedScript.getScript().sort("Int")), sum);
				final Term t = mManagedScript.getScript().term("ite", cond, constant, variable.getTermVariable());
				summarizedSymbMemory.put(variable.getTermVariable(), t);
			}
		}

		final ArrayList<Term> pathSummaries = new ArrayList<>();

		final Substitution symMemSub = new Substitution(mManagedScript, summarizedSymbMemory);
		final Substitution kappaSub = new Substitution(mManagedScript, kappaTauRel);

		for (int i = 0; i < pathAssertions.size(); i++) {
			final Set<Term> asserts = new HashSet<>();
			for (final Term t : pathAssertions.get(i)) {
				asserts.add(kappaSub.transform(symMemSub.transform(t)));
			}
			final TermVariable[] taus = new TermVariable[kappas.size() - 1];
			final Term[] rangeTerms = new Term[kappas.size() - 1];
			int arrayIndex = 0;
			for (int j = 0; j < kappas.size(); j++) {
				if (j != i) {
					taus[arrayIndex] = (TermVariable) kappaTauRel.get(kappas.get(j));
					rangeTerms[arrayIndex] = mManagedScript.getScript().term("<",
							Rational.ZERO.toTerm(mManagedScript.getScript().sort("Int")),
							kappaTauRel.get(kappas.get(j)),
							kappas.get(j));
					arrayIndex++;
				}
			}
			// todo: case for only one path; no exists etc
			// todo: case for no asserts in path
			final Term range = rangeTerms.length > 1 ?
					mManagedScript.getScript().term("and", rangeTerms) : rangeTerms[0];
			final Term[] params = new Term[asserts.size()];
			asserts.toArray(params);
			final Term pathSum = asserts.size() > 1 ?
					mManagedScript.getScript().term("and", asserts.toArray(new Term[asserts.size()])) :
					asserts.iterator().next();
			final Term summaryBody = mManagedScript.getScript().term("and", range, pathSum);
			final TermVariable[] existVariables = new TermVariable[kappaTauRel.keySet().size()];
			kappaTauRel.keySet().toArray(existVariables);
			final Term exists = mManagedScript.getScript().quantifier(0, taus, summaryBody, (Term []) null);
			final TermVariable[] pathTau = new TermVariable[1];
			pathTau[0] = (TermVariable) kappaTauRel.get(kappas.get(i));
			final Term forAll = mManagedScript.getScript().quantifier(1, pathTau, exists, (Term[]) null);
			mLogger.debug(forAll);
			pathSummaries.add(forAll);
		}

		final Term loopSummary = mManagedScript.getScript().term("and",
				pathSummaries.toArray(new Term[pathSummaries.size()]));
		mLogger.debug(loopSummary.toStringDirect());

		return null;
	}

	private void updateSymbolicMemory(final Term term, final TermVariable kappa, final IProgramVar assignedVar,
			final Map<IProgramVar, Term> symbolicMem, final Map<IProgramVar, TermVariable> inVars,
			final Set<TermVariable> assignedKappas, final Set<Term> kappaTerms) {
		final Term oldVal = symbolicMem.get(assignedVar);
		if (term instanceof ConstantTerm) {
			symbolicMem.put(assignedVar, term);
		} else if (term instanceof ApplicationTerm) {
			if (inVars.containsKey(assignedVar)) {
				if ("+".equals(((ApplicationTerm) term).getFunction().getName())
						|| "-".equals(((ApplicationTerm) term).getFunction().getName())) {
					final ArrayList<Term> parameter = new ArrayList<>();
					for (final Term t : ((ApplicationTerm) term).getParameters()) {
						if (!(t instanceof TermVariable) || t != assignedVar.getTermVariable()) {
							parameter.add(t);
						}
					}
					final Term auxTerm;
					if (parameter.size() > 1) {
						final Term[] auxArray = new Term[parameter.size()];
						parameter.toArray(auxArray);
						auxTerm = mManagedScript.getScript().term("+", auxArray);
					} else {
						auxTerm = parameter.get(0);
					}
					final Term summary = mManagedScript.getScript().term("*", auxTerm, kappa);
					if (oldVal != null) {
						symbolicMem.put(assignedVar, mManagedScript.getScript().term("+", oldVal, summary));
					} else {
						symbolicMem.put(assignedVar,
								mManagedScript.getScript().term("+", assignedVar.getTermVariable(), summary));
					}
					assignedKappas.add(kappa);
					kappaTerms.add(summary);
				} else {
				}
			} else {
				symbolicMem.put(assignedVar, term);
			}
		} else if (term instanceof TermVariable) {
			symbolicMem.put(assignedVar, term);
		} else {
			// TODO: Exception
		}
	}

	private Term cleanVariables(final Term term, final Map<IProgramVar, TermVariable> inVars) {
		if (term instanceof ConstantTerm) {
			return term;
		} else if (term instanceof TermVariable) {
			for (final IProgramVar ipv : inVars.keySet()) {
				if (inVars.get(ipv) == term) {
					return ipv.getTermVariable();
				}
			}
		} else if (term instanceof ApplicationTerm) {
			final Term[] tArray = new Term[((ApplicationTerm) term).getParameters().length];
			for (int i = 0; i < tArray.length; i++) {
				tArray[i] = cleanVariables(((ApplicationTerm) term).getParameters()[i], inVars);
			}
			return mManagedScript.getScript().term(((ApplicationTerm) term).getFunction().getName(), tArray);
		}
		return null;
	}

	private Term[] toDnf(final Term term) {
		final Dnf dnf = new Dnf(mManagedScript, mServices);
		final Term transFormedTerm = dnf.transform(term);
		return SmtUtils.getDisjuncts(transFormedTerm);
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResult;
	}

}
