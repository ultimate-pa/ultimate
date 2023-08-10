/*
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.TermContextTransformationEngine.DescendResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.TermContextTransformationEngine.TermWalker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolyPoNeUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.CondisDepthCodeGenerator.CondisDepthCode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.Context;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.Context.CcTransformation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;

/**
 * Simplification that is based on the ideas of {@link SimplifyDDA}. Unlike
 * {@link SimplifyDDA} we do not use an SMT solver but check implications only
 * pairwise implications between polynomials. Like {@link SimplifyDDA} we use
 * the context of subformulas (resp. the polynomials in the context for
 * implications checks). This simplification is less effective that
 * {@link SimplifyDDA} because we cannot detect implications that involve more
 * than two literals. However this simplification is usually much faster than
 * {@link SimplifyDDA}. In some cases it could be more effective than
 * {@link SimplifyDDA} because currently {@link SimplifyDDA} considers
 * quantified subformulas as atoms. <br />
 * TOOO 20210421 Matthias: There is still some room for improving efficiency.
 * Currently we transform very often the same terms to
 * {@link PolynomialRelation}s. We could store the the context as
 * {@link PolynomialRelation}s instead of terms or add a cache from which one
 * can obtain the {@link PolynomialRelation} of a term.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class PolyPacSimplificationTermWalker extends TermWalker<Term> {
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;
	/**
	 * Replace terms of the form `x = l ∧ φ(x)` by `x = l ∧ φ(l)` and replace terms
	 * of the form `x ≠ l ∨ φ(x)` by `x ≠ l ∨ φ(l)`, where l is a literal (of sort
	 * Real, Int, or BitVec) and x is a variable in a {@link PolynomialRelation}
	 * (E.g., a {@link TermVariable}, a constant symbol (0-ary function symbol), a
	 * select term `(select a k)`.)
	 */
	private static final boolean APPLY_CONSTANT_FOLDING = true;
	private static final boolean DEBUG_CHECK_RESULT = false;

	private PolyPacSimplificationTermWalker(final IUltimateServiceProvider services, final ManagedScript mgdScript) {
		super();
		mServices = services;
		mMgdScript = mgdScript;
	}

	@Override
	protected Term constructContextForApplicationTerm(final Term context, final FunctionSymbol symb,
			final List<Term> allParams, final int selectedParam) {
		return Context.buildCriticalConstraintForConDis(mServices, mMgdScript, context, symb, allParams, selectedParam,
				CcTransformation.TO_NNF);
	}

	@Override
	protected Term constructContextForQuantifiedFormula(final Term context, final int quant,
			final List<TermVariable> vars) {
		return Context.buildCriticalContraintForQuantifiedFormula(mMgdScript.getScript(), context, vars,
				CcTransformation.TO_NNF);
	}

	@Override
	protected DescendResult convert(final Term context, final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getFunction().getName().equals("and") || appTerm.getFunction().getName().equals("or")) {
				if (SmtUtils.isFalseLiteral(context)) {
					// Optimization for cases in which context is "false"
					// TODO 20210802 Matthias: check if this optimization
					// is still needed
					final Term result;
					if (appTerm.getFunction().getName().equals("and")) {
						result = mMgdScript.getScript().term("true");
					} else if (appTerm.getFunction().getName().equals("or")) {
						result = mMgdScript.getScript().term("false");
					} else {
						throw new AssertionError();
					}
					return new TermContextTransformationEngine.FinalResultForAscend(result);
				} else {
					return new TermContextTransformationEngine.IntermediateResultForDescend(term);
				}
			}
		} else if (term instanceof QuantifiedFormula) {
			return new TermContextTransformationEngine.IntermediateResultForDescend(term);
		}
		if (APPLY_CONSTANT_FOLDING) {
			final Map<Term, Term> substitutionMapping = new HashMap<>();
			for (final Term conjunct : SmtUtils.getConjuncts(context)) {
				if (!SmtUtils.isFunctionApplication(conjunct, "=")) {
					continue;
				}
				final PolynomialRelation polyRel = PolynomialRelation.of(mMgdScript.getScript(), conjunct);
				if (polyRel != null) {
					final SolvedBinaryRelation sbr = polyRel.isSimpleEquality(mMgdScript.getScript());
					if (sbr != null) {
						substitutionMapping.put(sbr.getLeftHandSide(), sbr.getRightHandSide());
					}
				}
			}
			if (!substitutionMapping.isEmpty()) {
				final Term renamed = Substitution.apply(mMgdScript, substitutionMapping, term);
				if (renamed != term) {
					return new TermContextTransformationEngine.FinalResultForAscend(renamed);
				}
			}
		}
		return new TermContextTransformationEngine.FinalResultForAscend(term);
	}

	@Override
	protected Term constructResultForApplicationTerm(final Term context, final ApplicationTerm originalApplicationTerm,
			final Term[] resultParams) {
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			final CondisDepthCode contextCdc = CondisDepthCode.of(context);
			throw new ToolchainCanceledException(this.getClass(),
					String.format("simplifying %s xjuncts wrt. a %s context", resultParams.length, contextCdc));
		}
		if (originalApplicationTerm.getFunction().getName().equals("and")) {
			return PolyPoNeUtils.and(mMgdScript.getScript(), context, Arrays.asList(resultParams));
		}
		if (originalApplicationTerm.getFunction().getName().equals("or")) {
			return PolyPoNeUtils.or(mMgdScript.getScript(), context, Arrays.asList(resultParams));
		}
		throw new AssertionError();
	}

	public static Term simplify(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final Term term) {
		final Term result = simplify(services, mgdScript, mgdScript.getScript().term("true"), term);
		if (DEBUG_CHECK_RESULT) {
			final boolean tolerateUnknown = true;
			SmtUtils.checkLogicalEquivalenceForDebugging(mgdScript.getScript(), result, term, PolyPoNeUtils.class,
					tolerateUnknown);
		}
		return result;
	}

	public static Term simplify(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final Term context, final Term term) {
		final Term result;
		try {
			final Comparator<Term> siblingOrder = null;
			result = TermContextTransformationEngine.transform(new PolyPacSimplificationTermWalker(services, mgdScript),
					siblingOrder, context, term);
		} catch (final ToolchainCanceledException tce) {
			final CondisDepthCode termCdc = CondisDepthCode.of(term);
			final String taskDescription = String.format("simplifying a %s term", termCdc);
			tce.addRunningTaskInfo(new RunningTaskInfo(PolyPacSimplificationTermWalker.class, taskDescription));
			throw tce;
		}
		return result;
	}

	@Override
	protected Term constructResultForQuantifiedFormula(final Term context,
			final QuantifiedFormula originalQuantifiedFormula, final Term resultSubformula) {
		return SmtUtils.quantifier(mMgdScript.getScript(), originalQuantifiedFormula.getQuantifier(),
				Arrays.asList(originalQuantifiedFormula.getVariables()), resultSubformula);
	}

	@Override
	protected boolean applyRepeatedlyUntilNoChange() {
		return true;
	}

	@Override
	protected void checkIntermediateResult(final Term context, final Term input, final Term output) {
		final LBool lBool = SmtUtils.checkEquivalenceUnderAssumption(input, output, context, mMgdScript.getScript());
		switch (lBool) {
		case SAT:
			throw new AssertionError(String.format(
					"Intermediate result not equivalent. Input: %s Output: %s Assumption: %s", input, output, context));
		case UNKNOWN:
			final ILogger logger = mServices.getLoggingService().getLogger(this.getClass());
			logger.info((String.format(
					"Insufficient ressources to check equivalence of intermediate result. Input: %s Output: %s Assumption: %s",
					input, output, context)));
			break;
		case UNSAT:
			break;
		default:
			throw new AssertionError("unknown value: " + lBool);
		}
	}

}
