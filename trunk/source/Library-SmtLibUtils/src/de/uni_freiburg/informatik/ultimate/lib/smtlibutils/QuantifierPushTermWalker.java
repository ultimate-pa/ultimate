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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils;

import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.ExtendedSimplificationResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.TermContextTransformationEngine.DescendResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.TermContextTransformationEngine.TermWalker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolyPoNeUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.EliminationTask;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.FormulaClassification;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.SimplificationOccasion;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class QuantifierPushTermWalker extends TermWalker<Context> {
	private final ManagedScript mMgdScript;

	private final IUltimateServiceProvider mServices;

	private final PqeTechniques mPqeTechniques;

	private final SimplificationTechnique mSimplificationTechnique;

	private final boolean mApplyDistributivity;

	private static final boolean DEBUG_CHECK_RESULT = false;

	private static final boolean CHECK_SIMPLIFICATION_POTENTIAL_OF_INPUT_AND_OUTPUT = true;

	public QuantifierPushTermWalker(final IUltimateServiceProvider services, final boolean applyDistributivity,
			final PqeTechniques pqeTechniques, final SimplificationTechnique simplificationTechnique,
			final ManagedScript mgdScript) {
		super();
		mServices = services;
		mApplyDistributivity = applyDistributivity;
		mPqeTechniques = pqeTechniques;
		mMgdScript = mgdScript;
		mSimplificationTechnique = simplificationTechnique;
	}

	@Override
	Context constructContextForApplicationTerm(final Context context,
			final FunctionSymbol symb, final List<Term> allParams, final int selectedParam) {
		return context.constructChildContextForConDis(mServices, mMgdScript, symb, allParams, selectedParam);
	}

	@Override
	Context constructContextForQuantifiedFormula(final Context context, final int quant,
			final List<TermVariable> vars) {
		return context.constructChildContextForQuantifiedFormula(mMgdScript.getScript(), vars);
	}

	@Override
	DescendResult convert(final Context context, final Term term) {
		FormulaClassification classification = null;
		Term currentTerm = PolyPacSimplificationTermWalker.simplify(mServices, mMgdScript, context.getCriticalConstraint(), term);
				//PolyPoNeUtils.and(mMgdScript.getScript(), context.getCriticalConstraint(), Collections.singleton(term));
		int iterations = 0;
		while (true) {
			classification = QuantifierPusher.classify(currentTerm);
			switch (classification) {
			case NOT_QUANTIFIED: {
				// let's recurse, there may be quantifiers in subformulas
				if (SmtUtils.isAtomicFormula(currentTerm)) {
					currentTerm = QuantifierPusher.simplify(mServices, mMgdScript, SimplificationOccasion.ATOM,
							SimplificationTechnique.POLY_PAC, context, currentTerm);
					currentTerm = QuantifierPusher.simplify(mServices, mMgdScript, SimplificationOccasion.ATOM,
							mSimplificationTechnique, context, currentTerm);
					return new TermContextTransformationEngine.FinalResultForAscend(currentTerm);
				} else {
					final Term negated = SmtUtils.unzipNot(currentTerm);
					if (negated != null && SmtUtils.isAtomicFormula(negated)) {
						currentTerm = QuantifierPusher.simplify(mServices, mMgdScript, SimplificationOccasion.ATOM,
								SimplificationTechnique.POLY_PAC, context, currentTerm);
						currentTerm = QuantifierPusher.simplify(mServices, mMgdScript, SimplificationOccasion.ATOM,
								mSimplificationTechnique, context, currentTerm);
						return new TermContextTransformationEngine.FinalResultForAscend(currentTerm);
					} else {
						return new TermContextTransformationEngine.IntermediateResultForDescend(currentTerm);
					}
				}
			}
			case SAME_QUANTIFIER: {
				currentTerm = QuantifierUtils.flattenQuantifiers(mMgdScript.getScript(), (QuantifiedFormula) currentTerm);
				break;
			}
			case DUAL_QUANTIFIER: {
				final Context childContext = context.constructChildContextForQuantifiedFormula(mMgdScript.getScript(),
						Arrays.asList(((QuantifiedFormula) currentTerm).getVariables()));
				final EliminationTask et = new EliminationTask((QuantifiedFormula) currentTerm, childContext);
				final Term tmp = QuantifierPusher.processDualQuantifier(mServices, mMgdScript,
						mApplyDistributivity, mPqeTechniques, mSimplificationTechnique, et,
						QuantifierPushTermWalker::eliminate);
				final FormulaClassification tmpClassification = QuantifierPusher.classify(tmp);
				if (tmpClassification == FormulaClassification.DUAL_QUANTIFIER) {
					// unable to push, we have to take this subformula as result
					return new TermContextTransformationEngine.FinalResultForAscend(tmp);
				} else {
					currentTerm = tmp;
					break;
				}
			}
			case CORRESPONDING_FINITE_CONNECTIVE: {
				currentTerm = QuantifierPusher.pushOverCorrespondingFiniteConnective(mMgdScript.getScript(), (QuantifiedFormula) currentTerm);
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
				} else {
					currentTerm = tmp;
					break;
				}
			}
			case DUAL_FINITE_CONNECTIVE: {
				final EliminationTask et = new EliminationTask((QuantifiedFormula) currentTerm, context);
				final Term tmp = QuantifierPusher.tryToPushOverDualFiniteConnective(mServices, mMgdScript,
						mApplyDistributivity, mPqeTechniques, mSimplificationTechnique, et,
						QuantifierPushTermWalker::eliminate);
				if (tmp == null) {
					// no more eliminations possible
					// let's recurse, there may be quantifiers in subformulas
					final Term res = QuantifierPusher.pushInner(mServices, mMgdScript, mApplyDistributivity,
							mPqeTechniques, mSimplificationTechnique, context.getBoundByAncestors(),
							(QuantifiedFormula) currentTerm, context.getCriticalConstraint(),
							QuantifierPushTermWalker::eliminate);
					return new TermContextTransformationEngine.FinalResultForAscend(res);
				} else {
					currentTerm = tmp;
					break;
				}
			}
			default:
				throw new AssertionError("unknown value " + classification);
			}
			iterations++;
		}
//		throw new AssertionError();
//
//
//
//
//		if (term instanceof ApplicationTerm) {
//			final ApplicationTerm appTerm = (ApplicationTerm) term;
//			if (appTerm.getFunction().getName().equals("and") || appTerm.getFunction().getName().equals("or")) {
//				return new TermContextTransformationEngine.IntermediateResultForDescend(term);
//			}
//		} else if (term instanceof QuantifiedFormula) {
//			return new TermContextTransformationEngine.IntermediateResultForDescend(term);
//		}
//		return new TermContextTransformationEngine.FinalResultForAscend<Term>(term);
	}



	@Override
	Term constructResultForApplicationTerm(final Context context, final ApplicationTerm originalApplicationTerm,
			final Term[] resultParams) {
		// TODO: Maybe full simplification with solver, maybe no simplification
		if (originalApplicationTerm.getFunction().getName().equals("and")) {
			return PolyPoNeUtils.and(mMgdScript.getScript(), context.getCriticalConstraint(), Arrays.asList(resultParams));
		}
		if (originalApplicationTerm.getFunction().getName().equals("or")) {
			return PolyPoNeUtils.or(mMgdScript.getScript(), context.getCriticalConstraint(), Arrays.asList(resultParams));
		}
		// TODO 20210516 Matthias: Decide whether we really want to support non-NNF
		// terms here.
		if (originalApplicationTerm.getFunction().getName().equals("=")) {
			return SmtUtils.equality(mMgdScript.getScript(), resultParams);
		}
		assert Arrays.equals(originalApplicationTerm.getParameters(), resultParams);
		return originalApplicationTerm;
	}

	@Override
	Term constructResultForQuantifiedFormula(final Context context, final QuantifiedFormula originalQuantifiedFormula,
			final Term resultSubformula) {
		return SmtUtils.quantifier(mMgdScript.getScript(), originalQuantifiedFormula.getQuantifier(),
				Arrays.asList(originalQuantifiedFormula.getVariables()), resultSubformula);
	}

	@Override
	boolean applyRepeatedlyUntilNoChange() {
		return false;
	}

	public static Term eliminate(final IUltimateServiceProvider services, final ManagedScript script,
			final boolean applyDistributivity, final PqeTechniques quantifierEliminationTechniques,
			final SimplificationTechnique simplificationTechnique, final Term inputTerm) {
		return eliminate(services, script, applyDistributivity, quantifierEliminationTechniques,
				simplificationTechnique, new Context(script.getScript()), inputTerm);
	}

	public static Term eliminate(final IUltimateServiceProvider services, final ManagedScript script,
			final boolean applyDistributivity, final PqeTechniques quantifierEliminationTechniques,
			final SimplificationTechnique simplificationTechnique, final Context context, final Term inputTerm) {
		if (CHECK_SIMPLIFICATION_POTENTIAL_OF_INPUT_AND_OUTPUT) {
			final ExtendedSimplificationResult esr = SmtUtils.simplifyWithStatistics(script, inputTerm, services,
					SimplificationTechnique.POLY_PAC);
			final String message = "Quantifier elimination called on non-simplified input: "
					+ esr.buildSizeReductionMessage();
			if (esr.getReductionRatioInPercent() < 100) {
				services.getLoggingService().getLogger(QuantifierPusher.class).warn(message);
			}
		}
		final Term result = TermContextTransformationEngine.transform(new QuantifierPushTermWalker(services,
				applyDistributivity, quantifierEliminationTechniques, simplificationTechnique, script), context,
				inputTerm);
		if (CHECK_SIMPLIFICATION_POTENTIAL_OF_INPUT_AND_OUTPUT) {
			final ExtendedSimplificationResult esr = SmtUtils.simplifyWithStatistics(script, result, services,
					SimplificationTechnique.POLY_PAC);
			final String message = "Quantifier elimination failed to simlify output: "
					+ esr.buildSizeReductionMessage();
			if (esr.getReductionRatioInPercent() < 100) {
				services.getLoggingService().getLogger(QuantifierPusher.class).warn(message);
			}
		}
		if (DEBUG_CHECK_RESULT) {
			final boolean tolerateUnknown = true;
			SmtUtils.checkLogicalEquivalenceForDebugging(script.getScript(), result, inputTerm, QuantifierPusher.class,
					tolerateUnknown);
		}
		return result;
	}

	@Override
	void checkIntermediateResult(final Context context, final Term input, final Term output) {
		final LBool lBool = SmtUtils.checkEquivalenceUnderAssumption(input, output, context.getCriticalConstraint(),
				mMgdScript.getScript());
		switch (lBool) {
		case SAT:
			throw new AssertionError(String.format(
					"Intermediate result not equivalent. Input: %s Output: %s Assumption: %s", input, output, context));
		case UNKNOWN:
			final ILogger logger = mServices.getLoggingService().getLogger(this.getClass());
			logger.warn(String.format(
					"Insufficient ressources to check equivalence of intermediate result. Input: %s Output: %s Assumption: %s",
					input, output, context));
			break;
		case UNSAT:
			break;
		default:
			throw new AssertionError("unknown value: " + lBool);
		}
	}

}
