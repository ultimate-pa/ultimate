/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.PrenexNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierSequence;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierSequence.QuantifiedVariables;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe.XjunctPartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe.XnfDer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe.XnfIrd;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe.XnfTir;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe.XnfUpd;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe.XnfUsr;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

/**
 * Try to eliminate existentially quantified variables in terms. Therefore we use that the term ∃v.v=c∧φ[v] is
 * equivalent to term φ[c]. Resp. we use that the term ∀v.v!=c∨φ[v] is equivalent to term φ[c].
 */
public class PartialQuantifierElimination {
	private static final boolean USE_UPD = true;
	private static final boolean USE_IRD = true;
	private static final boolean USE_TIR = true;
	private static final boolean USE_SSD = true;
	private static final boolean USE_AQE = false;
	private static final boolean USE_SOS = false;
	private static final boolean USE_USR = false;
	private static final boolean USE_PUSH_PULL = true;
	private static final boolean DEBUG_EXTENDED_RESULT_CHECK = false;
	private static final boolean DEBUG_APPLY_ARRAY_PQE_ALSO_TO_NEGATION = false;

	public static Term tryToEliminate(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript, final Term term, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		final Term withoutIte = (new IteRemover(mgdScript)).transform(term);
		final Term nnf = new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP).transform(withoutIte);
		final Term pushed = new QuantifierPusher(mgdScript, services, true, PqeTechniques.ALL_LOCAL).transform(nnf);
		final Term pnf = new PrenexNormalForm(mgdScript).transform(pushed);
		final QuantifierSequence qs = new QuantifierSequence(mgdScript.getScript(), pnf);
		final Term matrix = qs.getInnerTerm();
		final List<QuantifiedVariables> qvs = qs.getQuantifierBlocks();
		Term result = matrix;
		// if (qvs.size() > 1) {
		// throw new AssertionError("Attention!!! quantifier alternation " + qvs.size());
		// }
		for (int i = qvs.size() - 1; i >= 0; i--) {
			final QuantifiedVariables qv = qvs.get(i);
			final Set<TermVariable> eliminatees = new HashSet<>(qv.getVariables());
			try {
				result = elim(mgdScript, qv.getQuantifier(), eliminatees, result, services, logger,
						simplificationTechnique, xnfConversionTechnique);
			} catch (final ToolchainCanceledException tce) {
				final RunningTaskInfo rti = new RunningTaskInfo(PartialQuantifierElimination.class,
						"eliminating quantifiers from formula with " + (qvs.size() - 1) + " quantifier alternations");
				tce.addRunningTaskInfo(rti);
				throw tce;
			}
			result = SmtUtils.quantifier(mgdScript.getScript(), qv.getQuantifier(), eliminatees, result);
			result = new QuantifierPusher(mgdScript, services, true, PqeTechniques.ONLY_DER).transform(result);
		}
		return result;
	}

	/**
	 * Returns equivalent formula. Quantifier is dropped if quantified variable not in formula. Quantifier is eliminated
	 * if this can be done by the complete quantifier elimination.
	 */
	public static Term quantifier(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final int quantifier,
			final Collection<TermVariable> vars, final Term body, final Term[]... patterns) {
		Set<TermVariable> varSet = constructIntersectionWithFreeVars(vars, body);
		if (varSet.isEmpty()) {
			return body;
		}
		Term elim = body;
		if (USE_PUSH_PULL) {
			// final int quantBefore = varSet.size();
			// Set<TermVariable> varSet = new HashSet<TermVariable>(Arrays.asList(vars));
			elim = elimPushPull(mgdScript, quantifier, varSet, elim, services, logger);
			// return elim;
			if (elim instanceof QuantifiedFormula) {
				final QuantifiedFormula qf = (QuantifiedFormula) elim;
				varSet = new HashSet<>(Arrays.asList(qf.getVariables()));
				elim = qf.getSubformula();
				// final int quantAfterwards = varSet.size();
				// logger.warn("push-pull eliminated " + (quantBefore-quantAfterwards) + " of " + quantBefore);
			} else {
				// logger.warn("push-pull eliminated " + quantBefore);
				return elim;
			}
		}
		try {
			elim = elim(mgdScript, quantifier, varSet, elim, services, logger, simplificationTechnique,
					xnfConversionTechnique);
		} catch (final ToolchainCanceledException tce) {
			final String taskDescription = "eliminating quantifiers";
			tce.addRunningTaskInfo(new RunningTaskInfo(PartialQuantifierElimination.class, taskDescription));
			throw tce;
		}
		if (varSet.isEmpty()) {
			return elim;
		}
		return mgdScript.getScript().quantifier(quantifier, varSet.toArray(new TermVariable[varSet.size()]), elim,
				patterns);
	}

	/**
	 * Returns formula equivalent to the one constructed by {@link SmtUtils#quantifier(Script, int, Set, Term)}. Formula
	 * is not quantified if quantified variables are not in the formula or if quantifiers can be eliminated by using the
	 * specified {@link PqeTechniques}.
	 */
	public static Term quantifierCustom(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript, final PqeTechniques techniques, final int quantifier,
			final Collection<TermVariable> vars, final Term body, final Term[]... patterns) {
		final Set<TermVariable> varSet = constructIntersectionWithFreeVars(vars, body);
		if (varSet.isEmpty()) {
			return body;
		}
		final Term elim = elimPushPull(mgdScript, quantifier, varSet, body, services, logger, techniques);
		if (elim instanceof QuantifiedFormula) {
			final QuantifiedFormula qf = (QuantifiedFormula) elim;
			return mgdScript.getScript().quantifier(quantifier, qf.getVariables(), qf.getSubformula(), patterns);
		}
		return elim;
	}

	private static Set<TermVariable> constructIntersectionWithFreeVars(final Collection<TermVariable> vars,
			final Term term) {
		final Set<TermVariable> freeVars = new HashSet<>(Arrays.asList(term.getFreeVars()));
		final Set<TermVariable> occurringVars = new HashSet<>();
		for (final TermVariable tv : vars) {
			if (freeVars.contains(tv)) {
				occurringVars.add(tv);
			}
		}
		return occurringVars;
	}

	public static Term elimPushPull(final ManagedScript mgdScript, final int quantifier,
			final Set<TermVariable> eliminatees, final Term term, final IUltimateServiceProvider services,
			final ILogger logger) {
		return elimPushPull(mgdScript, quantifier, eliminatees, term, services, logger, PqeTechniques.ALL_LOCAL);
	}

	private static Term elimPushPull(final ManagedScript mgdScript, final int quantifier,
			final Set<TermVariable> eliminatees, final Term term, final IUltimateServiceProvider services,
			final ILogger logger, final PqeTechniques techniques) {
		final Term withoutIte = (new IteRemover(mgdScript)).transform(term);
		final Term nnf = new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP).transform(withoutIte);
		final Term quantified = mgdScript.getScript().quantifier(quantifier,
				eliminatees.toArray(new TermVariable[eliminatees.size()]), nnf);
		final Term pushed = new QuantifierPusher(mgdScript, services, true, techniques).transform(quantified);
		// final Term commu = new CommuhashNormalForm(services, mgdScript.getScript()).transform(pushed);
		// final Term pnf = new Nnf(script, services, freshTermVariableConstructor,
		// QuantifierHandling.PULL).transform(pushed);
		final Term pnf = new PrenexNormalForm(mgdScript).transform(pushed);
		return pnf;
	}

	public static Term elim(final ManagedScript mgdScript, final int quantifier, final Set<TermVariable> eliminatees,
			final Term term, final IUltimateServiceProvider services, final ILogger logger,
			final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		final Script script = mgdScript.getScript();
		final Set<TermVariable> occuringVars = new HashSet<>(Arrays.asList(term.getFreeVars()));
		final Iterator<TermVariable> it = eliminatees.iterator();
		while (it.hasNext()) {
			final TermVariable tv = it.next();
			if (!occuringVars.contains(tv)) {
				it.remove();
			}
		}
		if (eliminatees.isEmpty()) {
			return term;
		}
		Term result;

		// transform to DNF (resp. CNF)
		result = (new IteRemover(mgdScript)).transform(term);
		result = QuantifierUtils.transformToXnf(services, script, quantifier, mgdScript, result,
				xnfConversionTechnique);
		// if (result instanceof QuantifiedFormula) {
		// QuantifiedFormula qf = (QuantifiedFormula) result;
		// if (qf.getQuantifier() != quantifier) {
		// throw new UnsupportedOperationException("quantifier alternation unsupported! input: " + result);
		// }
		// eliminatees.addAll(Arrays.asList(qf.getVariables()));
		// result = qf.getSubformula();
		// }

		// apply Destructive Equality Resolution
		Term termAfterDER;
		{
			final XnfDer xnfDer = new XnfDer(mgdScript, services);
			final Term[] oldParams = QuantifierUtils.getXjunctsOuter(quantifier, result);
			final Term[] newParams = new Term[oldParams.length];
			for (int i = 0; i < oldParams.length; i++) {
				final Set<TermVariable> eliminateesDER = new HashSet<>(eliminatees);
				final Term[] oldAtoms = QuantifierUtils.getXjunctsInner(quantifier, oldParams[i]);
				newParams[i] = QuantifierUtils.applyDualFiniteConnective(script, quantifier,
						Arrays.asList(xnfDer.tryToEliminate(quantifier, oldAtoms, eliminateesDER)));
			}
			termAfterDER = QuantifierUtils.applyCorrespondingFiniteConnective(script, quantifier, newParams);
			result = termAfterDER;
			final Set<TermVariable> remainingAfterDER = new HashSet<>(eliminatees);
			remainingAfterDER.retainAll(Arrays.asList(result.getFreeVars()));
			eliminatees.retainAll(remainingAfterDER);
		}

		if (eliminatees.isEmpty()) {
			return result;
		}

		if (USE_IRD) {
			// apply Infinity Restrictor Drop
			result = applyInfinityRestrictorDrop(mgdScript, quantifier, eliminatees, services, script, result);
		}

		if (eliminatees.isEmpty()) {
			return result;
		}

		// apply TIR
		if (USE_TIR) {
			result = applyTir(mgdScript, quantifier, eliminatees, services, xnfConversionTechnique, script, result);
		}

		if (eliminatees.isEmpty()) {
			return result;
		}

		// apply Unconnected Parameter Deletion
		if (USE_UPD) {
			result = applyUnconnectedParameterDeletion(mgdScript, quantifier, eliminatees, services,
					xnfConversionTechnique, script, result);
		}
		if (USE_AQE) {

			final EliminationTask inputEliminationTask = new EliminationTask(quantifier, eliminatees, result);
			final EliminationTask esp = new ArrayQuantifierEliminationMain(mgdScript, services, simplificationTechnique)
					.elimAllRec(new EliminationTask(quantifier, eliminatees, result));

			assert validateEquivalence(script, inputEliminationTask, esp, logger, "SDD") : "Array QEs incorrect. Esp: "
					+ esp + " Input:" + inputEliminationTask;
			result = esp.getTerm();
			eliminatees.clear();
			eliminatees.addAll(esp.getEliminatees());
		}
		if (USE_SSD) {
			final long startTime = System.currentTimeMillis();
			final EliminationTask inputEliminationTask = new EliminationTask(quantifier, eliminatees, result);
			final EliminationTask esp = new ElimStorePlain(mgdScript, services, simplificationTechnique)
					.startRecursiveElimination(new EliminationTask(quantifier, eliminatees, result));
			final long duration = System.currentTimeMillis() - startTime;
			if (duration > 10_000) {
//				throw new AssertionError("long elimination: " + duration + "ms");
			}


			assert validateEquivalence(script, inputEliminationTask, esp, logger, "SDD") : "Array QEs incorrect. Esp: "
					+ esp + " Input:" + inputEliminationTask;
			if (DEBUG_APPLY_ARRAY_PQE_ALSO_TO_NEGATION) {
				final int quantifierNegated = (quantifier * -1) + 1;
				final Term negatedInput = new NnfTransformer(mgdScript, services, QuantifierHandling.CRASH)
						.transform(SmtUtils.not(mgdScript.getScript(), result));
				final EliminationTask espNegated = new ElimStorePlain(mgdScript, services, simplificationTechnique)
						.elimAll(new EliminationTask(quantifierNegated, eliminatees, negatedInput));
				espNegated.toString();
				if (esp.getEliminatees().size() != espNegated.getEliminatees().size()) {
					throw new AssertionError("different number of auxVars: esp " + esp.getEliminatees().size()
							+ " nesp " + espNegated.getEliminatees().size() + "Input: " + result);
				}
			}
			if (DEBUG_EXTENDED_RESULT_CHECK) {
				final EliminationTask sosResult = applyStoreOverSelect(mgdScript, quantifier, eliminatees, services,
						logger, simplificationTechnique, script, result);
				assert validateEquivalence(script, sosResult, esp, logger, "SDD") : "Array QEs differ. Esp: " + esp
						+ " Sos:" + sosResult;
				final boolean doSizeCheck = false;
				if (doSizeCheck) {
					final long espTreeSize = new DAGSize().treesize(esp.getTerm());
					final long sosTreeSize = new DAGSize().treesize(sosResult.getTerm());
					assert espTreeSize <= sosTreeSize * 2 : "unexpected size! esp:" + espTreeSize + " sos"
							+ sosTreeSize;
					if (sosTreeSize > 1 && sosTreeSize * 2 < espTreeSize) {
						throw new AssertionError("unexpected size! esp:" + espTreeSize + " sos" + sosTreeSize);
					}
				}
			}
			result = esp.getTerm();
			eliminatees.clear();
			eliminatees.addAll(esp.getEliminatees());
		}

		if (eliminatees.isEmpty()) {
			return result;
		}
		final boolean sosChangedTerm;
		// apply Store Over Select
		if (USE_SOS) {
			final EliminationTask sosResult = applyStoreOverSelect(mgdScript, quantifier, eliminatees, services, logger,
					simplificationTechnique, script, result);
			eliminatees.retainAll(sosResult.getEliminatees());
			eliminatees.addAll(sosResult.getEliminatees());
			sosChangedTerm = (result != sosResult.getTerm());
			result = sosResult.getTerm();
		} else {
			sosChangedTerm = false;
		}

		if (eliminatees.isEmpty()) {
			return result;
		}

		// simplification
		// result = SmtUtils.simplify(mgdScript, result, services, simplificationTechnique);

		// (new SimplifyDDA(script)).getSimplifiedTerm(result);
		eliminatees.retainAll(Arrays.asList(result.getFreeVars()));

		// if (!eliminateesBeforeSOS.containsAll(eliminatees)) {
		// SOS introduced new variables that should be eliminated
		if (sosChangedTerm) {
			// if term was changed by SOS new elimination might be possible
			// Before the implementation of IRD we only retried elimination
			// if SOS introduced more quantified variables.
			result = elim(mgdScript, quantifier, eliminatees, result, services, logger, simplificationTechnique,
					xnfConversionTechnique);
		}

		if (eliminatees.isEmpty()) {
			return result;
		}

		assert Arrays.asList(result.getFreeVars()).containsAll(eliminatees) : "superficial variables";

		if (USE_USR) {
			result = applyUsr(mgdScript, quantifier, eliminatees, services, logger, simplificationTechnique,
					xnfConversionTechnique, script, result);
		}

		return result;
	}

	private static boolean validateEquivalence(final Script script, final EliminationTask inputEliminationTask,
			final EliminationTask esp, final ILogger logger, final String name) {
		final LBool sat = EliminationTask.areDistinct(script, esp, inputEliminationTask);
		if (sat == LBool.UNKNOWN) {
			logger.warn("Trying to double check " + name + " result, but SMT solver's response was UNKNOWN.");
			logger.warn("Input elimination task: " + inputEliminationTask);
			logger.warn("ElimStorePlain result: " + esp);

		}
		return sat != LBool.SAT;
	}

	private static Term applyInfinityRestrictorDrop(final ManagedScript mgdScript, final int quantifier,
			final Set<TermVariable> eliminatees, final IUltimateServiceProvider services, final Script script,
			final Term resultOld) {
		final XnfIrd xnfIRD = new XnfIrd(mgdScript, services);
		final Term[] oldParams = QuantifierUtils.getXjunctsOuter(quantifier, resultOld);
		final Term[] newParams = new Term[oldParams.length];
		for (int i = 0; i < oldParams.length; i++) {
			final Set<TermVariable> eliminateesIRD = new HashSet<>(eliminatees);
			final Term[] oldAtoms = QuantifierUtils.getXjunctsInner(quantifier, oldParams[i]);
			newParams[i] = QuantifierUtils.applyDualFiniteConnective(script, quantifier,
					Arrays.asList(xnfIRD.tryToEliminate(quantifier, oldAtoms, eliminateesIRD)));
		}
		final Term termAfterIRD = QuantifierUtils.applyCorrespondingFiniteConnective(script, quantifier, newParams);
		final Set<TermVariable> remainingAfterIRD = new HashSet<>(eliminatees);
		remainingAfterIRD.retainAll(Arrays.asList(termAfterIRD.getFreeVars()));
		eliminatees.retainAll(remainingAfterIRD);
		return termAfterIRD;
	}

	private static Term applyTir(final ManagedScript mgdScript, final int quantifier,
			final Set<TermVariable> eliminatees, final IUltimateServiceProvider services,
			final XnfConversionTechnique xnfConversionTechnique, final Script script, final Term resultOld) {
		final XnfTir xnfTir = new XnfTir(mgdScript, services, xnfConversionTechnique);
		final Term termAfterTIR = applyEliminationOuter(script, quantifier, eliminatees, resultOld, xnfTir, services,
				mgdScript, xnfConversionTechnique);
		return termAfterTIR;
	}

	private static Term applyUnconnectedParameterDeletion(final ManagedScript mgdScript, final int quantifier,
			final Set<TermVariable> eliminatees, final IUltimateServiceProvider services,
			final XnfConversionTechnique xnfConversionTechnique, final Script script, final Term resultOld) {
		final XnfUpd xnfUpd = new XnfUpd(mgdScript, services);
		final Term termAfterUPD = applyEliminationOuter(script, quantifier, eliminatees, resultOld, xnfUpd, services,
				mgdScript, xnfConversionTechnique);
		return termAfterUPD;
	}

	private static EliminationTask applyStoreOverSelect(final ManagedScript mgdScript, final int quantifier,
			final Set<TermVariable> eliminatees, final IUltimateServiceProvider services, final ILogger logger,
			final SimplificationTechnique simplificationTechnique, final Script script, final Term resultOld) {
		final Set<TermVariable> remainingAndNewAfterSOS = new HashSet<>();
		final Term[] oldParams = QuantifierUtils.getXjunctsOuter(quantifier, resultOld);
		final Term[] newParams = new Term[oldParams.length];
		for (int i = 0; i < oldParams.length; i++) {
			final Set<TermVariable> eliminateesSOS = new HashSet<>(eliminatees);
			newParams[i] = sos(script, quantifier, oldParams[i], eliminateesSOS, logger, services, mgdScript,
					simplificationTechnique);
			remainingAndNewAfterSOS.addAll(eliminateesSOS);
		}
		final Term termAfterSOS = QuantifierUtils.applyCorrespondingFiniteConnective(script, quantifier, newParams);
		return new EliminationTask(quantifier, remainingAndNewAfterSOS, termAfterSOS);
	}

	private static Term applyUsr(final ManagedScript mgdScript, final int quantifier,
			final Set<TermVariable> eliminatees, final IUltimateServiceProvider services, final ILogger logger,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final Script script, final Term resultOld) {
		final XnfUsr xnfUsr = new XnfUsr(mgdScript, services);
		final Term[] oldParams = QuantifierUtils.getXjunctsOuter(quantifier, resultOld);
		final Term[] newParams = new Term[oldParams.length];
		for (int i = 0; i < oldParams.length; i++) {
			final Set<TermVariable> eliminateesUsr = new HashSet<>(eliminatees);
			final Term[] oldAtoms = QuantifierUtils.getXjunctsInner(quantifier, oldParams[i]);
			newParams[i] = QuantifierUtils.applyDualFiniteConnective(script, quantifier,
					Arrays.asList(xnfUsr.tryToEliminate(quantifier, oldAtoms, eliminateesUsr)));
		}
		Term termAfterUsr = QuantifierUtils.applyCorrespondingFiniteConnective(script, quantifier, newParams);
		if (!xnfUsr.getAffectedEliminatees().isEmpty()) {
			termAfterUsr = elim(mgdScript, quantifier, eliminatees, termAfterUsr, services, logger,
					simplificationTechnique, xnfConversionTechnique);
		}
		return termAfterUsr;
	}

	private static Term applyEliminationOuter(final Script script, final int quantifier,
			final Set<TermVariable> eliminatees, final Term term, final XjunctPartialQuantifierElimination elimination,
			final IUltimateServiceProvider services, final ManagedScript freshTermVariableConstructor,
			final XnfConversionTechnique xnfConversionTechnique) {
		final Term[] oldXjunctsOuter = QuantifierUtils.getXjunctsOuter(quantifier, term);
		final Term[] newXjunctsOuter = new Term[oldXjunctsOuter.length];
		for (int i = 0; i < oldXjunctsOuter.length; i++) {
			final HashSet<TermVariable> localEliminatees =
					constructIntersectionWithFreeVars(eliminatees, oldXjunctsOuter[i]);
			if (localEliminatees.isEmpty()) {
				newXjunctsOuter[i] = oldXjunctsOuter[i];
			} else {
				newXjunctsOuter[i] =
						applyEliminationInner(script, quantifier, localEliminatees, oldXjunctsOuter[i], elimination);
				if (quantifier == QuantifiedFormula.EXISTS) {
					if (SmtUtils.isTrueLiteral(newXjunctsOuter[i])) {
						eliminatees.clear();
						return script.term("true");
					}
				} else if (quantifier == QuantifiedFormula.FORALL) {
					if (SmtUtils.isFalseLiteral(newXjunctsOuter[i])) {
						eliminatees.clear();
						return script.term("false");
					}
				} else {
					throw new AssertionError("unknown quantifier");
				}
			}
		}
		Term result = QuantifierUtils.applyCorrespondingFiniteConnective(script, quantifier, newXjunctsOuter);
		final Set<TermVariable> remainingEliminatees = new HashSet<>(eliminatees);
		remainingEliminatees.retainAll(Arrays.asList(result.getFreeVars()));
		eliminatees.retainAll(remainingEliminatees);
		if (!elimination.resultIsXjunction()) {
			result = QuantifierUtils.transformToXnf(services, script, quantifier, freshTermVariableConstructor, result,
					xnfConversionTechnique);
		}
		return result;
	}

	private static Term applyEliminationInner(final Script script, final int quantifier,
			final Set<TermVariable> eliminatees, final Term term,
			final XjunctPartialQuantifierElimination elimination) {
		final Set<TermVariable> eliminateesCopy = new HashSet<>(eliminatees);
		final Term[] oldXjunctsInner = QuantifierUtils.getXjunctsInner(quantifier, term);
		final Term[] newXjunctsInner = elimination.tryToEliminate(quantifier, oldXjunctsInner, eliminateesCopy);
		final Term result =
				QuantifierUtils.applyDualFiniteConnective(script, quantifier, Arrays.asList(newXjunctsInner));
		return result;
	}

	/**
	 * Construct a new HashSet that contains all TermVariables that are in vars and occur as free variable in term.
	 */
	private static HashSet<TermVariable> constructIntersectionWithFreeVars(final Set<TermVariable> vars,
			final Term term) {
		final HashSet<TermVariable> result = new HashSet<>();
		for (final TermVariable tv : term.getFreeVars()) {
			if (vars.contains(tv)) {
				result.add(tv);
			}
		}
		return result;
	}

	public static Term sos(final Script script, final int quantifier, final Term term,
			final Set<TermVariable> eliminatees, final ILogger logger, final IUltimateServiceProvider services,
			final ManagedScript freshTermVariableConstructor, final SimplificationTechnique simplicationTechnique) {
		Term result = term;
		final Set<TermVariable> overallAuxVars = new HashSet<>();
		final Iterator<TermVariable> it = eliminatees.iterator();
		while (it.hasNext()) {
			final TermVariable tv = it.next();
			if (tv.getSort().isArraySort()) {
				// if (quantifier != QuantifiedFormula.EXISTS) {
				// // return term;
				// throw new
				// UnsupportedOperationException("QE for universal quantified arrays not implemented yet.");
				// }
				final Set<TermVariable> thisIterationAuxVars = new HashSet<>();
				final Term elim =
						(new ElimStore3(script, freshTermVariableConstructor, services, simplicationTechnique))
								.elim(quantifier, tv, result, thisIterationAuxVars);
				logger.debug(new DebugMessage("eliminated quantifier via SOS for {0}, additionally introduced {1}", tv,
						thisIterationAuxVars));
				overallAuxVars.addAll(thisIterationAuxVars);
				// if (Arrays.asList(elim.getFreeVars()).contains(tv)) {
				// elim = (new ElimStore3(script)).elim(tv, result,
				// thisIterationAuxVars);
				// }
				assert !Arrays.asList(elim.getFreeVars()).contains(tv) : "var is still there";
				result = elim;
			}
		}
		eliminatees.addAll(overallAuxVars);
		return result;
	}

	// /**
	// * Try to eliminate the variables vars = {x_1,...,x_n} in term φ_1∧...∧φ_m.
	// * Therefore we use the following approach, which we call Unconnected
	// * Parameter Drop. If X is a subset of {x_1,...,x_n} and Φ is a subset
	// * {φ_1,...,φ_m} such that - variables in X occur only in term of Φ, and -
	// * terms in Φ contain only variables of X, and - the conjunction of all term
	// * in Φ is satisfiable. Then we can remove the conjuncts Φ and the
	// * quantified variables X from φ_1∧...∧φ_m and obtain an equivalent formula.
	// *
	// * Is only sound if there are no uninterpreted function symbols in the term
	// * TODO: extend this to uninterpreted function symbols (for soundness)
	// *
	// * @param logger
	// */
	// public static Term updSimple(Script script, int quantifier, Term term, Set<TermVariable> vars, ILogger logger) {
	// Set<TermVariable> occuringVars = new HashSet<TermVariable>(Arrays.asList(term.getFreeVars()));
	// vars.retainAll(occuringVars);
	// Set<Term> parameters;
	// if (quantifier == QuantifiedFormula.EXISTS) {
	// parameters = new HashSet<Term>(Arrays.asList(SmtUtils.getConjuncts(term)));
	// } else if (quantifier == QuantifiedFormula.FORALL) {
	// parameters = new HashSet<Term>(Arrays.asList(SmtUtils.getDisjuncts(term)));
	// } else {
	// throw new AssertionError("unknown quantifier");
	// }
	// ConnectionPartition connection = new ConnectionPartition(parameters);
	// List<TermVariable> removeableTvs = new ArrayList<TermVariable>();
	// List<TermVariable> unremoveableTvs = new ArrayList<TermVariable>();
	// List<Term> removeableTerms = new ArrayList<Term>();
	// List<Term> unremoveableTerms = new ArrayList<Term>();
	// for (Set<Term> connectedTerms : connection.getConnectedVariables()) {
	// Set<TermVariable> connectedVars = SmtUtils.getFreeVars(connectedTerms);
	// boolean isSuperfluous;
	// if (quantifier == QuantifiedFormula.EXISTS) {
	// Term simplified = isSuperfluousConjunction(script, connectedTerms, connectedVars, vars);
	// if (SmtUtils.isTrue(simplified)) {
	// isSuperfluous = true;
	// } else if (SmtUtils.isFalse(simplified)) {
	// return simplified;
	// } else if (simplified == null) {
	// isSuperfluous = false;
	// } else {
	// throw new AssertionError("illegal case");
	// }
	// } else if (quantifier == QuantifiedFormula.FORALL) {
	// Term simplified = isSuperfluousDisjunction(script, connectedTerms, connectedVars, vars);
	// if (SmtUtils.isFalse(simplified)) {
	// isSuperfluous = true;
	// } else if (SmtUtils.isTrue(simplified)) {
	// return simplified;
	// } else if (simplified == null) {
	// isSuperfluous = false;
	// } else {
	// throw new AssertionError("illegal case");
	// }
	// } else {
	// throw new AssertionError("unknown quantifier");
	// }
	// if (isSuperfluous) {
	// removeableTvs.addAll(connectedVars);
	// removeableTerms.addAll(connectedTerms);
	// } else {
	// unremoveableTvs.addAll(connectedVars);
	// unremoveableTerms.addAll(connectedTerms);
	// }
	// }
	// List<Term> termsWithoutTvs = connection.getTermsWithOutTvs();
	// assert occuringVars.size() == removeableTvs.size() + unremoveableTvs.size();
	// assert parameters.size() == removeableTerms.size() + unremoveableTerms.size() + termsWithoutTvs.size();
	// for (Term termWithoutTvs : termsWithoutTvs) {
	// LBool sat = Util.checkSat(script, termWithoutTvs);
	// if (sat == LBool.UNSAT) {
	// if (quantifier == QuantifiedFormula.EXISTS) {
	// vars.clear();
	// return script.term("false");
	// } else if (quantifier == QuantifiedFormula.FORALL) {
	// // we drop this term its equivalent to false
	// } else {
	// throw new AssertionError("unknown quantifier");
	// }
	// } else if (sat == LBool.SAT) {
	// if (quantifier == QuantifiedFormula.EXISTS) {
	// // we drop this term its equivalent to true
	// } else if (quantifier == QuantifiedFormula.FORALL) {
	// vars.clear();
	// return script.term("true");
	// } else {
	// throw new AssertionError("unknown quantifier");
	// }
	// } else {
	// throw new AssertionError("expecting sat or unsat");
	// }
	// }
	// if (removeableTerms.isEmpty()) {
	// logger.debug(new DebugMessage("not eliminated quantifier via UPD for {0}", occuringVars));
	// return term;
	// } else {
	// vars.removeAll(removeableTvs);
	// logger.debug(new DebugMessage("eliminated quantifier via UPD for {0}", removeableTvs));
	// Term result;
	// if (quantifier == QuantifiedFormula.EXISTS) {
	// result = SmtUtils.and(script, unremoveableTerms.toArray(new Term[unremoveableTerms.size()]));
	// } else if (quantifier == QuantifiedFormula.FORALL) {
	// result = SmtUtils.or(script, unremoveableTerms.toArray(new Term[unremoveableTerms.size()]));
	// } else {
	// throw new AssertionError("unknown quantifier");
	// }
	// return result;
	// }
	// }

	/**
	 * Return "true" if connectedVars is a subset of quantifiedVars and the conjunction of terms is satisfiable. Return
	 * "false" if connectedVars is a subset of quantifiedVars and the conjunction of terms is not satisfiable. Return
	 * null otherwise
	 */
	public static Term isSuperfluousConjunction(final Script script, final Set<Term> terms,
			final Set<TermVariable> connectedVars, final Set<TermVariable> quantifiedVars) {
		if (quantifiedVars.containsAll(connectedVars)) {
			final Term conjunction = SmtUtils.and(script, terms.toArray(new Term[terms.size()]));
			final LBool isSat = Util.checkSat(script, conjunction);
			if (isSat == LBool.SAT) {
				return script.term("true");
			} else if (isSat == LBool.UNSAT) {
				return script.term("false");
			}
		}
		return null;
	}

	/**
	 * Return "false" if connectedVars is a subset of quantifiedVars and the conjunction of terms is not valid. Return
	 * "true" if connectedVars is a subset of quantifiedVars and the conjunction of terms is valid. Return null
	 * otherwise
	 */
	public static Term isSuperfluousDisjunction(final Script script, final Set<Term> terms,
			final Set<TermVariable> connectedVars, final Set<TermVariable> quantifiedVars) {
		if (quantifiedVars.containsAll(connectedVars)) {
			final Term disjunction = SmtUtils.or(script, terms.toArray(new Term[terms.size()]));
			final LBool isSat = Util.checkSat(script, SmtUtils.not(script, disjunction));
			if (isSat == LBool.SAT) {
				return script.term("false");
			} else if (isSat == LBool.UNSAT) {
				return script.term("true");
			}
		}
		return null;
	}

	/**
	 * Find term φ such that term implies tv == φ.
	 *
	 * @param logger
	 */
	private static Term findEqualTermExists(final TermVariable tv, final Term term, final ILogger logger) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final FunctionSymbol sym = appTerm.getFunction();
			final Term[] params = appTerm.getParameters();
			if (sym.getName().equals("=")) {
				final int tvOnOneSideOfEquality = tvOnOneSideOfEquality(tv, params, logger);
				if (tvOnOneSideOfEquality == -1) {
					return null;
				}
				assert (tvOnOneSideOfEquality == 0 || tvOnOneSideOfEquality == 1);
				return params[tvOnOneSideOfEquality];
			} else if (sym.getName().equals("and")) {
				for (final Term param : params) {
					final Term equalTerm = findEqualTermExists(tv, param, logger);
					if (equalTerm != null) {
						return equalTerm;
					}
				}
				return null;
			} else {
				return null;
			}
		}
		return null;
	}

	/**
	 * Find term φ such that tv != φ implies term
	 *
	 * @param logger
	 */
	private static Term findEqualTermForall(final TermVariable tv, final Term term, final ILogger logger) {
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			FunctionSymbol sym = appTerm.getFunction();
			Term[] params = appTerm.getParameters();
			if (sym.getName().equals("not")) {
				assert params.length == 1;
				if (params[0] instanceof ApplicationTerm) {
					appTerm = (ApplicationTerm) params[0];
					sym = appTerm.getFunction();
					params = appTerm.getParameters();
					if (sym.getName().equals("=")) {
						final int tvOnOneSideOfEquality = tvOnOneSideOfEquality(tv, params, logger);
						if (tvOnOneSideOfEquality == -1) {
							return null;
						}
						assert (tvOnOneSideOfEquality == 0 || tvOnOneSideOfEquality == 1);
						return params[tvOnOneSideOfEquality];
					}
					return null;
				}
				return null;
			} else if (sym.getName().equals("or")) {
				for (final Term param : params) {
					final Term equalTerm = findEqualTermForall(tv, param, logger);
					if (equalTerm != null) {
						return equalTerm;
					}
				}
				return null;
			} else {
				return null;
			}
		}
		return null;
	}

	/**
	 * return
	 * <ul>
	 * <li>0 if right hand side of equality is tv and left hand side does not contain tv
	 * <li>1 if left hand side of equality is tv and right hand side does not contain tv
	 * <li>-1 otherwise
	 * </ul>
	 *
	 * @param logger
	 */
	private static int tvOnOneSideOfEquality(final TermVariable tv, final Term[] params, final ILogger logger) {
		if (params.length != 2) {
			logger.warn("Equality of length " + params.length);
		}
		if (params[0] == tv) {
			final boolean rightHandSideContainsTv = Arrays.asList(params[1].getFreeVars()).contains(tv);
			if (rightHandSideContainsTv) {
				return -1;
			}
			return 1;
		} else if (params[1] == tv) {
			final boolean leftHandSideContainsTv = Arrays.asList(params[0].getFreeVars()).contains(tv);
			if (leftHandSideContainsTv) {
				return -1;
			}
			return 0;
		}
		return -1;
	}

	// public static Term usr(Script script, int quantifier, Term term, Collection<TermVariable> eliminatees,
	// Set<TermVariable> affectedEliminatees, ILogger logger) {
	// Term[] oldParams;
	// if (quantifier == QuantifiedFormula.EXISTS) {
	// oldParams = SmtUtils.getConjuncts(term);
	// } else if (quantifier == QuantifiedFormula.FORALL) {
	// oldParams = SmtUtils.getDisjuncts(term);
	// } else {
	// throw new AssertionError("unknown quantifier");
	// }
	// HashRelation<TermVariable, Term> var2arrays = new HashRelation<TermVariable, Term>();
	// HashRelation<TermVariable, Term> var2parameters = new HashRelation<TermVariable, Term>();
	// for (Term param : oldParams) {
	// List<MultiDimensionalSelect> slects = MultiDimensionalSelect.extractSelectDeep(param, false);
	// for (MultiDimensionalSelect mds : slects) {
	// Set<TermVariable> indexFreeVars = mds.getIndex().getFreeVars();
	// for (TermVariable tv : indexFreeVars) {
	// if (eliminatees.contains(tv)) {
	// var2arrays.addPair(tv, mds.getArray());
	// var2parameters.addPair(tv, param);
	// }
	// }
	// }
	// }
	// Set<Term> superfluousParams = new HashSet<Term>();
	// for (TermVariable eliminatee : var2arrays.getDomain()) {
	// if (var2arrays.getImage(eliminatee).size() == 1 &&
	// var2parameters.getImage(eliminatee).size() == 1) {
	// superfluousParams.addAll(var2parameters.getImage(eliminatee));
	// affectedEliminatees.add(eliminatee);
	// }
	// }
	// ArrayList<Term> resultParams = new ArrayList<Term>();
	// for (Term oldParam : oldParams) {
	// if (!superfluousParams.contains(oldParam)) {
	// resultParams.add(oldParam);
	// }
	// }
	// return SmtUtils.and(script, resultParams.toArray(new Term[resultParams.size()]));
	// }

	/**
	 * Construct new set that contains all Term variables that occur in eliminatees and are free variables of term.
	 *
	 * @return
	 */
	public static Set<TermVariable> constructNewEliminatees(final Term term, final Set<TermVariable> eliminatees) {
		final Set<TermVariable> result = new HashSet<>();
		for (final TermVariable tv : term.getFreeVars()) {
			if (eliminatees.contains(tv)) {
				result.add(tv);
			}
		}
		return result;
	}
}
