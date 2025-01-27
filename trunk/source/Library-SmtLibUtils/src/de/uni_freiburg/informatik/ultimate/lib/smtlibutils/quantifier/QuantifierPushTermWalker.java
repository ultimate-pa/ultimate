/*
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier;

import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PolyPacSimplificationTermWalker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.ExtendedSimplificationResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.TermContextTransformationEngine;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.TermContextTransformationEngine.DescendResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.TermContextTransformationEngine.TermWalker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolyPoNeUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.FormulaClassification;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.SimplificationOccasion;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

public class QuantifierPushTermWalker extends TermWalker<Context> {

	private static final boolean OPTION_APPLY_REPEATEDLY_UNTIL_NOCHANGE = false;
	/**
	 * Note that this is useless if
	 * {@link QuantifierPushTermWalker#OPTION_APPLY_REPEATEDLY_UNTIL_NOCHANGE} is
	 * set.
	 */
	private static final boolean OPTION_SIMPLIFY_CONSTRUCTED_APPLICATION_TERMS = true;

	private static final boolean DEBUG_CHECK_RESULT = false;
	private static final boolean DEBUG_CHECK_SIMPLIFICATION_POTENTIAL_OF_INPUT_AND_OUTPUT = false;


	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;
	private final PqeTechniques mPqeTechniques;
	private final SimplificationTechnique mSimplificationTechnique;
	private final boolean mApplyDistributivity;


	/**
	 * This class provides the new (2020) quantifier elimination and replaces the
	 * now deprecated {@link QuantifierPusher}. The purpose of this class is to
	 * traverse the formula and to call {@link DualJunctionQuantifierElimination}s
	 * which to the explicit eliminations and to call simplifications. This class
	 * does a stack-based traversal that uses
	 * {@link TermContextTransformationEngine} instead of an explicit recursion
	 * based on java methods.
	 *
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 *
	 */
	private QuantifierPushTermWalker(final IUltimateServiceProvider services, final boolean applyDistributivity,
			final PqeTechniques pqeTechniques, final SimplificationTechnique simplificationTechnique,
			final ManagedScript mgdScript) {
		mServices = services;
		mApplyDistributivity = applyDistributivity;
		mPqeTechniques = pqeTechniques;
		mMgdScript = mgdScript;
		mSimplificationTechnique = simplificationTechnique;
	}

	@Override
	protected Context constructContextForApplicationTerm(final Context context, final FunctionSymbol symb,
			final List<Term> allParams, final int selectedParam) {
		return context.constructChildContextForConDis(mServices, mMgdScript, symb, allParams, selectedParam);
	}

	@Override
	protected Context constructContextForQuantifiedFormula(final Context context, final int quant,
			final List<TermVariable> vars) {
		return context.constructChildContextForQuantifiedFormula(mMgdScript.getScript(), vars);
	}

	@Override
	protected
	DescendResult convert(final Context context, final Term term) {
		FormulaClassification classification = null;
		// 20220502 Matthias: If you remove the PolyPac simplification here, it should
		// be at least done for atoms (which are handled in one of the cases below)
		// 20220706 Matthias: The underlying {@link TermContextTransformationEngine}
		// does not simplify this level, e.g., if one of the siblings is the absorbing
		// element for the connective. If you remove this simplification here, you have
		// to improve the {@link TermContextTransformationEngine} (probably by something
		// similar than this PolyPac simplification).
		Term currentTerm = PolyPacSimplificationTermWalker.simplify(mServices, mMgdScript,
				context.getCriticalConstraint(), term);
		int iterations = 0;
		while (true) {
			classification = QuantifierPusher.classify(currentTerm);
			switch (classification) {
			case NOT_QUANTIFIED: {
				// let's recurse, there may be quantifiers in subformulas
				if (SmtUtils.isAtomicFormula(currentTerm)) {
					if (!SmtUtils.isTrueLiteral(currentTerm) && !SmtUtils.isFalseLiteral(currentTerm)) {
						currentTerm = QuantifierPusher.simplify(mServices, mMgdScript, SimplificationOccasion.ATOM,
								mSimplificationTechnique, context, currentTerm);
					}
					return new TermContextTransformationEngine.FinalResultForAscend(currentTerm);
				}
				final Term negated = SmtUtils.unzipNot(currentTerm);
				if (negated != null && SmtUtils.isAtomicFormula(negated)) {
					currentTerm = QuantifierPusher.simplify(mServices, mMgdScript, SimplificationOccasion.ATOM,
							mSimplificationTechnique, context, currentTerm);
					return new TermContextTransformationEngine.FinalResultForAscend(currentTerm);
				}
				return new TermContextTransformationEngine.IntermediateResultForDescend(currentTerm);
			}
			case SAME_QUANTIFIER: {
				currentTerm =
						QuantifierUtils.flattenQuantifiers(mMgdScript.getScript(), (QuantifiedFormula) currentTerm);
				break;
			}
			case DUAL_QUANTIFIER: {
				final Context childContext = context.constructChildContextForQuantifiedFormula(mMgdScript.getScript(),
						Arrays.asList(((QuantifiedFormula) currentTerm).getVariables()));
				final EliminationTask et = new EliminationTask((QuantifiedFormula) currentTerm, childContext);
				final Term tmp = QuantifierPusher.processDualQuantifier(mServices, mMgdScript, mApplyDistributivity,
						mPqeTechniques, mSimplificationTechnique, et, QuantifierPushTermWalker::eliminate);
				final FormulaClassification tmpClassification = QuantifierPusher.classify(tmp);
				if (tmpClassification == FormulaClassification.DUAL_QUANTIFIER) {
					// unable to push, we have to take this subformula as result
					return new TermContextTransformationEngine.FinalResultForAscend(tmp);
				}
				currentTerm = tmp;
				break;
			}
			case CORRESPONDING_FINITE_CONNECTIVE: {
				currentTerm = QuantifierPusher.pushOverCorrespondingFiniteConnective(mMgdScript.getScript(),
						(QuantifiedFormula) currentTerm);
				assert currentTerm != null : "corresponding connective case must never fail";
				break;
			}
			case ATOM: {
				final Term tmp = QuantifierPusher.applyEliminationToAtom(mServices, mMgdScript, mApplyDistributivity,
						mPqeTechniques, context, (QuantifiedFormula) currentTerm);
				if (tmp == null) {
					// no more eliminations possible
					// let's recurse, there may be quantifiers in subformulas
					final Term res = QuantifierPusher.pushInner(mServices, mMgdScript, mApplyDistributivity,
							mPqeTechniques, mSimplificationTechnique, context.getBoundByAncestors(),
							(QuantifiedFormula) currentTerm, context.getCriticalConstraint(),
							QuantifierPushTermWalker::eliminate);
					return new TermContextTransformationEngine.FinalResultForAscend(res);
				}
				currentTerm = tmp;
				break;
			}
			case DUAL_FINITE_CONNECTIVE: {
				final EliminationTask et = new EliminationTask((QuantifiedFormula) currentTerm, context);
				final Term tmp =
						QuantifierPusher.tryToPushOverDualFiniteConnective(mServices, mMgdScript, mApplyDistributivity,
								mPqeTechniques, mSimplificationTechnique, et, QuantifierPushTermWalker::eliminate);
				if (tmp == null) {
					// no more eliminations possible
					// let's recurse, there may be quantifiers in subformulas
					final Term res = QuantifierPusher.pushInner(mServices, mMgdScript, mApplyDistributivity,
							mPqeTechniques, mSimplificationTechnique, context.getBoundByAncestors(),
							(QuantifiedFormula) currentTerm, context.getCriticalConstraint(),
							QuantifierPushTermWalker::eliminate);
					return new TermContextTransformationEngine.FinalResultForAscend(res);
				}
				currentTerm = tmp;
				break;
			}
			default:
				throw new AssertionError("unknown value " + classification);
			}
			iterations++;
			if (iterations % 10 == 0) {
				final ILogger logger = mServices.getLoggingService().getLogger(QuantifierPusher.class);
				logger.info(String.format(
						"Run %s iterations without descend maybe there is a nontermination bug.",
						iterations));
			}
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(QuantifierPusher.class,
						String.format("running %s iterations on subformula", iterations));
			}
		}
	}

	@Override
	protected Term constructResultForApplicationTerm(final Context context,
			final ApplicationTerm originalApplicationTerm, final Term[] resultParams) {
		// TODO: Maybe full simplification with solver, maybe no simplification
		if (originalApplicationTerm.getFunction().getName().equals("and")) {
			final Term result;
			if (OPTION_SIMPLIFY_CONSTRUCTED_APPLICATION_TERMS) {
				final Term tmp = SmtUtils.and(mMgdScript.getScript(), resultParams);
				result = PolyPacSimplificationTermWalker.simplify(mServices, mMgdScript,
						context.getCriticalConstraint(), tmp);
			} else {
				result = PolyPoNeUtils.and(mMgdScript.getScript(), context.getCriticalConstraint(),
					Arrays.asList(resultParams));
			}
			return result;
		}
		if (originalApplicationTerm.getFunction().getName().equals("or")) {
			final Term result;
			if (OPTION_SIMPLIFY_CONSTRUCTED_APPLICATION_TERMS) {
				final Term tmp = SmtUtils.or(mMgdScript.getScript(), resultParams);
				result = PolyPacSimplificationTermWalker.simplify(mServices, mMgdScript,
						context.getCriticalConstraint(), tmp);
			} else {
				result = PolyPoNeUtils.or(mMgdScript.getScript(), context.getCriticalConstraint(),
					Arrays.asList(resultParams));
			}
			return result;
		}
		// TODO 20210516 Matthias: Decide whether we really want to support non-NNF
		// terms here.
		if (originalApplicationTerm.getFunction().getName().equals("=")) {
			final Term eq = SmtUtils.equality(mMgdScript.getScript(), resultParams);
			if (OPTION_SIMPLIFY_CONSTRUCTED_APPLICATION_TERMS) {
				return PolyPacSimplificationTermWalker.simplify(mServices, mMgdScript,
						context.getCriticalConstraint(), eq);
			} else {
				return eq;
			}
		}
		assert Arrays.equals(originalApplicationTerm.getParameters(), resultParams);
		return originalApplicationTerm;
	}

	@Override
	protected Term constructResultForQuantifiedFormula(final Context context,
			final QuantifiedFormula originalQuantifiedFormula, final Term resultSubformula) {
		return SmtUtils.quantifier(mMgdScript.getScript(), originalQuantifiedFormula.getQuantifier(),
				Arrays.asList(originalQuantifiedFormula.getVariables()), resultSubformula);
	}

	@Override
	protected boolean applyRepeatedlyUntilNoChange() {
		return OPTION_APPLY_REPEATEDLY_UNTIL_NOCHANGE;
	}

	/**
	 *
	 * @param inputTerm Term from which quantifiers are eliminated. Has to be in NNF.
	 */
	public static Term eliminate(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final boolean applyDistributivity, final PqeTechniques quantifierEliminationTechniques,
			final SimplificationTechnique simplificationTechnique, final Term inputTerm) {
		mgdScript.assertScriptNotLocked();
		return eliminate(services, mgdScript, applyDistributivity, quantifierEliminationTechniques,
				simplificationTechnique, new Context(mgdScript.getScript()), inputTerm);
	}

	/**
	 *
	 * @param inputTerm Term from which quantifiers are eliminated. Has to be in NNF.
	 */
	public static Term eliminate(final IUltimateServiceProvider services, final ManagedScript script,
			final boolean applyDistributivity, final PqeTechniques quantifierEliminationTechniques,
			final SimplificationTechnique simplificationTechnique, final Context context, final Term inputTerm) {
		checkSimplificationPotential(services, script, "Quantifier elimination called on non-simplified input",
				inputTerm);
		final Comparator<Term> siblingOrder = null;
		final Term result = TermContextTransformationEngine.transform(new QuantifierPushTermWalker(services,
				applyDistributivity, quantifierEliminationTechniques, simplificationTechnique, script), siblingOrder,
				context, inputTerm);
		checkSimplificationPotential(services, script, "Quantifier elimination failed to simlify output", result);
		if (DEBUG_CHECK_RESULT) {
			final boolean tolerateUnknown = true;
			SmtUtils.checkLogicalEquivalenceForDebugging(script.getScript(), result, inputTerm, QuantifierPusher.class,
					tolerateUnknown);
		}
		return result;
	}

	private static void checkSimplificationPotential(final IUltimateServiceProvider services,
			final ManagedScript script, final String msg, final Term inputTerm) {
		if (!DEBUG_CHECK_SIMPLIFICATION_POTENTIAL_OF_INPUT_AND_OUTPUT) {
			return;
		}
		final ExtendedSimplificationResult esr =
				SmtUtils.simplifyWithStatistics(script, inputTerm, services, SimplificationTechnique.POLY_PAC);
		final ILogger logger = services.getLoggingService().getLogger(QuantifierPusher.class);
		if (esr.getReductionRatioInPercent() < 100) {
			logger.warn("%s: %s (took %s)", msg, esr.buildSizeReductionMessage(),
					CoreUtil.humanReadableTime(esr.getSimplificationTimeNano(), TimeUnit.NANOSECONDS, 2));
		} else if (esr.getSimplificationTimeNano() > 5000000) {
			logger.warn("Useless simplification took %s: %s",
					CoreUtil.humanReadableTime(esr.getSimplificationTimeNano(), TimeUnit.NANOSECONDS, 2),
					esr.buildSizeReductionMessage());
		}
	}

	@Override
	protected void checkIntermediateResult(final Context context, final Term input, final Term output) {
		final LBool lBool = SmtUtils.checkEquivalenceUnderAssumption(input, output, context.getCriticalConstraint(),
				mMgdScript.getScript());
		switch (lBool) {
		case SAT:
			throw new AssertionError(
					String.format("Intermediate result not equivalent. Input: %s Output: %s Assumption: %s", input,
							output, context.getCriticalConstraint()));
		case UNKNOWN:
			final ILogger logger = mServices.getLoggingService().getLogger(this.getClass());
			logger.warn(String.format(
					"Insufficient ressources to check equivalence of intermediate result. Input: %s Output: %s Assumption: %s",
					input, output, context.getCriticalConstraint()));
			break;
		case UNSAT:
			break;
		default:
			throw new AssertionError("unknown value: " + lBool);
		}
	}

}
