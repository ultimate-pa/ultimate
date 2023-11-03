/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.MultiCaseSolvedBinaryRelation.IntricateOperation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.MultiCaseSolvedBinaryRelation.Xnf;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.INonSolverScript;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Auxiliary methods for {@link PolynomialRelation#solveForSubject}
 *
 * @author Leonard Fichtner
 * @author Max Barth
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class SolveForSubjectUtils {

	static MultiCaseSolvedBinaryRelation solveForSubject(final ManagedScript mgdScript, final Term subject,
			final MultiCaseSolvedBinaryRelation.Xnf xnf, final PolynomialRelation polyRel,
			final Set<TermVariable> bannedForDivCapture, final boolean allowDivModBasedSolutions) {
		MultiCaseSolvedBinaryRelation res;
		if (allowDivModBasedSolutions && SmtSortUtils.isNumericSort(subject.getSort())) {
			res = findTreatableDivModSubterm(mgdScript, subject, polyRel.getPolynomialTerm(), null, xnf,
					polyRel.toTerm(mgdScript.getScript()), bannedForDivCapture);
		} else {
			res = null;
		}
		if (res == null) {
			res = solveForSubjectWithoutTreatableDivMod(mgdScript.getScript(), subject, polyRel, xnf, bannedForDivCapture);
		}
		if (res == null) {
			return null;
		}
		assert res.isSubjectOnlyOnRhs() : "subject not only LHS";
		assert mgdScript instanceof INonSolverScript || SmtUtils.checkEquivalence(polyRel.toTerm(mgdScript.getScript()),
				res.toTerm(mgdScript.getScript()), mgdScript.getScript()) != LBool.SAT : "solveForSubject unsound";
		return res;
	}

	private static MultiCaseSolvedBinaryRelation solveForSubjectWithoutTreatableDivMod(final Script script,
			final Term subject, final PolynomialRelation polyRel, final MultiCaseSolvedBinaryRelation.Xnf xnf,
			final Set<TermVariable> bannedForDivCapture) throws AssertionError {

		final ExplicitLhsPolynomialRelation elpr =
				ExplicitLhsPolynomialRelation.moveMonomialToLhs(script, subject, polyRel);
		if (elpr == null) {
			return null;
		}
		ExplicitLhsPolynomialRelation solvedElpr = elpr.divInvertible(elpr.getLhsCoefficient());
		final IntricateOperation additionalIo;
		final Term intLiteralDivConstraint;
		if (solvedElpr == null) {
			if (SmtSortUtils.isRealSort(elpr.getLhsMonomial().getSort())) {
				throw new AssertionError();
			} else if (SmtSortUtils.isIntSort(elpr.getLhsMonomial().getSort())) {
				final Pair<ExplicitLhsPolynomialRelation, Term> tmp =
						elpr.divideByIntegerCoefficient(script, bannedForDivCapture);
				if (tmp == null) {
					return null;
				}
				solvedElpr = tmp.getFirst();
				additionalIo = IntricateOperation.DIV_BY_INTEGER_CONSTANT;
				intLiteralDivConstraint = tmp.getSecond();
			} else if (SmtSortUtils.isBitvecSort(elpr.getLhsMonomial().getSort())) {
				return null;
			} else {
				throw new AssertionError("unsupported sort");
			}
		} else {
			additionalIo = null;
			intLiteralDivConstraint = null;
		}
		if (solvedElpr.getLhsMonomial().isLinear()) {
			assert solvedElpr.getLhsMonomial().getSingleVariable().equals(subject);

			final MultiCaseSolutionBuilder mcsb = new MultiCaseSolutionBuilder(subject, xnf);
			final Collection<Case> cases = new ArrayList<>();
			final SolvedBinaryRelation sbr;
			if (additionalIo == null) {
				sbr = new SolvedBinaryRelation(solvedElpr.getLhsMonomial().getSingleVariable(),
						solvedElpr.getRhs().toTerm(script), solvedElpr.getRelationSymbol());
			} else {
				sbr = new SolvedBinaryRelation(solvedElpr.getLhsMonomial().getSingleVariable(),
						solvedElpr.getRhs().toTerm(script), solvedElpr.getRelationSymbol(), additionalIo);
			}
			final Set<SupportingTerm> supportingTerms;
			if (isDerIntegerDivisionSupportingTermRequired(xnf, subject.getSort(), solvedElpr.getRelationSymbol())
					&& intLiteralDivConstraint != null) {
				final SupportingTerm divisibilityConstraint =
						constructDerIntegerDivisionSupportingTerm(script, intLiteralDivConstraint);
				supportingTerms = Collections.singleton(divisibilityConstraint);
			} else {
				supportingTerms = Collections.emptySet();
			}
			cases.add(new Case(sbr, supportingTerms, xnf));

			if (isAntiDerIntegerDivisionCaseRequired(xnf, subject.getSort(), solvedElpr.getRelationSymbol())
					&& intLiteralDivConstraint != null) {
				final Set<SupportingTerm> suppTerms = new HashSet<>();
				final boolean negate = solvedElpr.getRelationSymbol().equals(RelationSymbol.DISTINCT);
				final Term divisibilityConstraintTerm = intLiteralDivConstraint;
				final SupportingTerm divisibilityConstraint = new SupportingTerm(divisibilityConstraintTerm,
						IntricateOperation.DIV_BY_INTEGER_CONSTANT, Collections.emptySet());
				suppTerms.add(divisibilityConstraint);
				// if (divisorAsArray.length > 1 || !(divisorAsArray[0] instanceof ConstantTerm)) {
				// final SupportingTerm inRelationToZero = constructInRelationToZeroSupportingTerm(script,
				// SmtUtils.mul(script, stageTwoRhs.getSort(), divisorAsArray),
				// negateForCnf(RelationSymbol.DISTINCT, xnf));
				// suppTerms.add(inRelationToZero);
				// }
				final Case result = new Case(null, suppTerms, xnf);
				cases.add(result);
			}

			mcsb.splitCases(cases);
			return mcsb.buildResult();
		}
		if (SmtSortUtils.isBitvecSort(elpr.getLhsMonomial().getSort())) {
			if (solvedElpr.getLhsMonomial().isLinear()) {
			} else {
				return null;
			}
		}
		return solvedElpr.divByMonomial(script, subject, xnf, bannedForDivCapture, intLiteralDivConstraint,
				additionalIo);
	}

	private static MultiCaseSolvedBinaryRelation tryToHandleDivModSubterm(final ManagedScript mgdScript, final Term subject,
			final MultiCaseSolvedBinaryRelation.Xnf xnf, final ApplicationTerm divModSubterm, final Term pnf,
			final Set<TermVariable> bannedForDivCapture) {
		final Term divisor = SmtUtils.mul(mgdScript.getScript(), "*",
				Arrays.copyOfRange(divModSubterm.getParameters(), 1, divModSubterm.getParameters().length));
		assert (divisor instanceof ConstantTerm) : "not constant";
		// Solve for subject in affineterm with a parameter of form (mod/div (subterm
		// with subject) constant)
		final Sort termSort = subject.getSort();
		// recVarName ensures different names in each recursion, since AffineRelation is
		// made new each time
		final int recVarName = divModSubterm.toString().length();
		final TermVariable auxDiv =
				mgdScript.variable(SmtUtils.removeSmtQuoteCharacters("aux_div_" + subject + "_" + recVarName), termSort);
		final TermVariable auxMod =
				mgdScript.variable(SmtUtils.removeSmtQuoteCharacters("aux_mod_" + subject + "_" + recVarName), termSort);
		if (Arrays.stream(pnf.getFreeVars()).anyMatch(x -> x.getName().equals(auxDiv.getName()))) {
			throw new AssertionError("Possible infinite loop detected " + auxDiv + " already exists");
		}
		if (Arrays.stream(pnf.getFreeVars()).anyMatch(x -> x.getName().equals(auxMod.getName()))) {
			throw new AssertionError("Possible infinite loop detected " + auxMod + " already exists");
		}

		final MultiCaseSolvedBinaryRelation solvedComparison;

		{
			final Term multiplication = SmtUtils.mul(mgdScript.getScript(), termSort, divisor, auxDiv);
			final Term sum = SmtUtils.sum(mgdScript.getScript(), termSort, auxMod, multiplication);
			final Term subtermSumComparison = BinaryRelation.toTerm(mgdScript.getScript(), negateForCnf(RelationSymbol.EQ, xnf),
					divModSubterm.getParameters()[0], sum);
			// recursive call for (= divident[subject] (+ (* aux_div divisor) aux_mod))
			final HashSet<TermVariable> bannedForDivCaptureWithAuxiliary = new HashSet<>(bannedForDivCapture);
			bannedForDivCaptureWithAuxiliary.add(auxDiv);
			bannedForDivCaptureWithAuxiliary.add(auxMod);
			solvedComparison = PolynomialRelation.of(mgdScript.getScript(), subtermSumComparison)
					.solveForSubject(mgdScript, subject, xnf, bannedForDivCaptureWithAuxiliary, true);
			if (solvedComparison == null) {
				return null;
			}
		}

		final MultiCaseSolutionBuilder mcsb = new MultiCaseSolutionBuilder(subject, xnf);
		// construct as SupportingTerm either
		// (= (div divident[subject] divisor) aux_div) or
		// (= (mod divident[subject] divisor) mod_div)
		final Set<TermVariable> setAuxVars = new LinkedHashSet<>();
		setAuxVars.add(auxMod);
		// substitute allowedSubterm with corresponding aux variable in input
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		if (SmtUtils.isIntMod(divModSubterm)) {
			substitutionMapping.put(divModSubterm, auxMod);
			mcsb.reportAdditionalAuxiliaryVariable(auxDiv);
		} else if (SmtUtils.isIntDiv(divModSubterm)) {
			setAuxVars.add(auxDiv);
			substitutionMapping.put(divModSubterm, auxDiv);
		} else {
			throw new AssertionError("input must be div or mod");
		}
		final List<Case> resultCases = new ArrayList<>();
		for (final Case c : solvedComparison.getCases()) {
			if (c.getSolvedBinaryRelation() != null) {
				substitutionMapping.put(subject, c.getSolvedBinaryRelation().getRightHandSide());
			}
			final Term auxModEqualsTerm = Substitution.apply(mgdScript, substitutionMapping, pnf);
			if (c.getSolvedBinaryRelation() == null) {
				final boolean containsSubject = SmtUtils.isSubterm(auxModEqualsTerm, subject);
				if (containsSubject) {
					// cannot solve, one Case has no SolvedBinaryRelation and the PolynomialRelation
					// contains the subject also outside the considered div/mod term.
					// TODO 20200612 Matthias: Optimization: Try to solve differently for this
					// case and use the other occurrence of the subject.
					// Complicated, but probably not yet relevant in practice.
					return null;
				}
			}
			final SupportingTerm auxEquals = new SupportingTerm(auxModEqualsTerm,
					IntricateOperation.MUL_BY_INTEGER_CONSTANT, new HashSet<>(setAuxVars));
			final Set<SupportingTerm> resultSupportingTerms = new HashSet<>(c.getSupportingTerms());
			resultSupportingTerms.add(auxEquals);
			final Case resultCase = new Case(c.getSolvedBinaryRelation(), resultSupportingTerms, xnf);
			resultCases.add(resultCase);
		}

		mcsb.splitCases(resultCases);
		for (final TermVariable add : solvedComparison.getAuxiliaryVariables()) {
			mcsb.reportAdditionalAuxiliaryVariable(add);
		}
		for (final IntricateOperation add : solvedComparison.getIntricateOperations()) {
			mcsb.reportAdditionalIntricateOperation(add);
		}

		// construct SupportingTerm (0 <= aux_mod)
		final Term auxModGreaterZeroTerm = BinaryRelation.toTerm(mgdScript.getScript(), negateForCnf(RelationSymbol.LEQ, xnf),
				Rational.ZERO.toTerm(termSort), auxMod);
		final SupportingTerm auxModGreaterZero =
				new SupportingTerm(auxModGreaterZeroTerm, IntricateOperation.MUL_BY_INTEGER_CONSTANT, setAuxVars);

		// construct SupportingTerm (aux_mod < abs(k))
		final Term auxModLessCoefTerm = BinaryRelation.toTerm(mgdScript.getScript(), negateForCnf(RelationSymbol.LESS, xnf), auxMod,
				SmtUtils.abs(mgdScript.getScript(), divisor));
		final SupportingTerm auxModLessCoef =
				new SupportingTerm(auxModLessCoefTerm, IntricateOperation.MUL_BY_INTEGER_CONSTANT, setAuxVars);

		mcsb.addAtoms(auxModLessCoef, auxModGreaterZero);
		final MultiCaseSolvedBinaryRelation result = mcsb.buildResult();
		assert result.isSubjectOnlyOnRhs() : "subject not only LHS";
		assert mgdScript instanceof INonSolverScript || SmtUtils.checkEquivalence(pnf, result.toTerm(mgdScript.getScript()),
				mgdScript.getScript()) != LBool.SAT : "solveForSubject unsound";
		return result;
	}

	/**
	 * If we divide an integer RHS, the result is nontrivial. If we just apply division some information related to
	 * divisibility is lost.
	 * <ul>
	 * <li>If the relation symbol is EQ or DISTINCT, the lost information is that the RHS was (resp. was not) divisible
	 * by the divisor. And can be added later.</li>
	 * <li>Otherwise, the lost information is more complicated, we can not easily add it later. Instead, we construct a
	 * more complicated quotient that depends on
	 * <ul>
	 * <li>the sign of the divident's values</li>
	 * <li>the relation symbol</li>
	 * </ul>
	 * and ensures that no information is lost.</li>
	 * </ul>
	 */
	@Deprecated
	private static Term constructRhsIntegerQuotient(final Script script, final RelationSymbol relSymb, final Term rhs,
			final boolean divisorIsPositive, final Term divisor) {
		final Term result;
		switch (relSymb) {
		case LESS:
			if (divisorIsPositive) {
				// k*x < t is equivalent to x < (t-1 div k)+1 for positive k
				result = constructRhsIntegerQuotientHelper(script, rhs, Rational.ONE, divisor);
			} else {
				// -k*x >= t is equivalent to x <= (t - 1 div -k) - 1
				result = constructRhsIntegerQuotientHelper(script, rhs, Rational.MONE, divisor);
			}
			break;
		case GREATER:
			// k*x > t is equivalent to x > (t div k) for all k
			result = SmtUtils.division(script, rhs.getSort(), prepend(rhs, divisor));
			break;
		case LEQ:
			// k*x <= t is equivalent to x <= (t div k) for positive k
			result = SmtUtils.division(script, rhs.getSort(), prepend(rhs, divisor));
			break;
		case GEQ:
			if (divisorIsPositive) {
				// k*x >= t is equivalent to x >= (t - 1 div k) + 1 for positive k
				result = constructRhsIntegerQuotientHelper(script, rhs, Rational.ONE, divisor);
			} else {
				// -k*x >= t is equivalent to x <= (t - 1 div -k) - 1
				result = constructRhsIntegerQuotientHelper(script, rhs, Rational.MONE, divisor);
			}
			break;
		case EQ:
			// Default quotient, additional divisibility information has to be added later
			result = SmtUtils.division(script, rhs.getSort(), prepend(rhs, divisor));
			break;
		case DISTINCT:
			// Default quotient, additional divisibility information has to be added later
			result = SmtUtils.division(script, rhs.getSort(), prepend(rhs, divisor));
			break;
		case BVULE:
		case BVULT:
		case BVUGE:
		case BVUGT:
		case BVSLE:
		case BVSLT:
		case BVSGE:
		case BVSGT:
			throw new AssertionError("bitvector relation with integer not possible: " + relSymb);
		default:
			throw new AssertionError("unknown relation symbol: " + relSymb);
		}
		return result;
	}

	/**
	 * If we divide an integer RHS, the result is nontrivial. If we just apply division some information related to
	 * divisibility is lost.
	 * <ul>
	 * <li>If the relation symbol is EQ or DISTINCT, the lost information is that the RHS was (resp. was not) divisible
	 * by the divisor. And can be added later.</li>
	 * <li>Otherwise, the lost information is more complicated, we can not easily add it later. Instead, we construct a
	 * more complicated quotient that depends on
	 * <ul>
	 * <li>the sign of the divident's values</li>
	 * <li>the relation symbol</li>
	 * </ul>
	 * and ensures that no information is lost.</li>
	 * </ul>
	 */
	public static IPolynomialTerm constructRhsIntegerQuotient(final Script script, final RelationSymbol relSymb,
			final IPolynomialTerm rhs, final boolean divisorIsPositive, final Term divisor,
			final Set<TermVariable> bannedForDivCapture) {
		final Rational preDivisionOffset;
		final Rational postDivisionOffset;
		switch (relSymb) {
		case LESS:
			if (divisorIsPositive) {
				// k*x < t is equivalent to x < (t-1 div k)+1 for positive k
				preDivisionOffset = Rational.MONE;
				postDivisionOffset = Rational.ONE;
			} else {
				// -k*x >= t is equivalent to x <= (t - 1 div -k) - 1
				preDivisionOffset = Rational.MONE;
				postDivisionOffset = Rational.MONE;
			}
			break;
		case GREATER:
			// k*x > t is equivalent to x > (t div k) for all k
			preDivisionOffset = Rational.ZERO;
			postDivisionOffset = Rational.ZERO;
			break;
		case LEQ:
			// k*x <= t is equivalent to x <= (t div k) for all k
			preDivisionOffset = Rational.ZERO;
			postDivisionOffset = Rational.ZERO;
			break;
		case GEQ:
			if (divisorIsPositive) {
				// k*x >= t is equivalent to x >= (t - 1 div k) + 1 for positive k
				preDivisionOffset = Rational.MONE;
				postDivisionOffset = Rational.ONE;
			} else {
				// -k*x >= t is equivalent to x <= (t - 1 div -k) - 1
				preDivisionOffset = Rational.MONE;
				postDivisionOffset = Rational.MONE;
			}
			break;
		case EQ:
			// Default quotient, additional divisibility information has to be added later
			preDivisionOffset = Rational.ZERO;
			postDivisionOffset = Rational.ZERO;
			break;
		case DISTINCT:
			// Default quotient, additional divisibility information has to be added later
			preDivisionOffset = Rational.ZERO;
			postDivisionOffset = Rational.ZERO;
			break;
		case BVULE:
		case BVULT:
		case BVUGE:
		case BVUGT:
		case BVSLE:
		case BVSLT:
		case BVSGE:
		case BVSGT:
			throw new AssertionError("bitvector relation with integer not possible: " + relSymb);
		default:
			throw new AssertionError("unknown relation symbol: " + relSymb);
		}
		final IPolynomialTerm beforeDiv;
		if (preDivisionOffset.equals(Rational.ZERO)) {
			beforeDiv = rhs;
		} else {
			beforeDiv = ((AbstractGeneralizedAffineTerm<?>) rhs).add(preDivisionOffset);
		}
		final IPolynomialTerm afterDiv;
		final Rational divisorAsRational = SmtUtils.tryToConvertToLiteral(divisor);
		if (divisorAsRational == null) {
			if (Arrays.stream(beforeDiv.toTerm(script).getFreeVars()).anyMatch(bannedForDivCapture::contains)) {
				afterDiv = null;
			} else {
				// Can't be simplified since the divisor is not a constant, construct
				// `div` term directly without {@link SmtUtils#div}.
				afterDiv = PolynomialTermOperations.convert(script,
						SmtUtils.divIntFlatten(script, beforeDiv.toTerm(script), divisor));
			}
		} else {
			if (!divisorAsRational.isIntegral()) {
				throw new AssertionError("expected int");
			}
			if (divisorAsRational.isNegative() == divisorIsPositive) {
				throw new AssertionError("inconsistent information on sign");
			}
			final BigInteger divisorAsInt = divisorAsRational.numerator();
			afterDiv = ((AbstractGeneralizedAffineTerm<?>) beforeDiv).divInt(script, divisorAsInt, bannedForDivCapture);
		}
		if (afterDiv == null) {
			return null;
		}
		final IPolynomialTerm result;
		if (postDivisionOffset.equals(Rational.ZERO)) {
			result = afterDiv;
		} else {
			result = ((AbstractGeneralizedAffineTerm<?>) afterDiv).add(postDivisionOffset);
		}
		return result;
	}

	/**
	 * Construct quotient
	 *
	 * <pre>
	 * ((divident - 1) / divisor) + postDivisionOffset
	 * </pre>
	 *
	 * which is required for LESS, GREATER, LEQ, and GEQ. See {@link PolynomialRelation#constructRhsIntegerQuotient}
	 *
	 * @param postDivisionOffset
	 *            value that is added after the division and that is determined from the relation symbol and the sign of
	 *            the divisor's values.
	 */
	@Deprecated
	private static Term constructRhsIntegerQuotientHelper(final Script script, final Term divident,
			final Rational postDivisionOffset, final Term divisor) {
		// The preDivisionOffset is always minus one.
		final Term preDivisionOffset = SmtUtils.rational2Term(script, Rational.MONE, divident.getSort());
		final Term divArgument = SmtUtils.sum(script, divident.getSort(), divident, preDivisionOffset);
		final Term simplifiedDivArgument =
				((IPolynomialTerm) (new PolynomialTermTransformer(script)).transform(divArgument)).toTerm(script);
		final Term[] result = prepend(simplifiedDivArgument, divisor);
		final Term quotient = SmtUtils.division(script, divident.getSort(), result);
		return SmtUtils.sum(script, divident.getSort(), quotient,
				SmtUtils.rational2Term(script, postDivisionOffset, divident.getSort()));
	}

	static Term[] prepend(final Term head, final Term... tail) {
		final List<Term> resultAsList = new ArrayList<>(tail.length + 1);
		resultAsList.add(head);
		resultAsList.addAll(Arrays.asList(tail));
		final Term[] resultArray = resultAsList.toArray(new Term[resultAsList.size()]);
		return resultArray;
	}

	/**
	 * @return true iff all params starting from index 1 are {@link ConstantTerm}s.
	 */
	public static boolean tailIsConstant(final List<Term> parameters) {
		assert parameters.size() > 1;
		final Iterator<Term> it = parameters.iterator();
		it.next();
		while (it.hasNext()) {
			if (!(it.next() instanceof ConstantTerm)) {
				return false;
			}
		}
		return true;
	}

	static RelationSymbol negateForCnf(final RelationSymbol symb, final Xnf xnf) {
		if (xnf == Xnf.CNF) {
			return symb.negate();
		} else {
			return symb;
		}
	}

	static boolean isDerIntegerDivisionSupportingTermRequired(final Xnf xnf, final Sort sort,
			final RelationSymbol relSymb) {
		return SmtSortUtils.isIntSort(sort) && ((relSymb == RelationSymbol.EQ) && xnf == Xnf.DNF
				|| (relSymb == RelationSymbol.DISTINCT) && xnf == Xnf.CNF);
	}

	static boolean isAntiDerIntegerDivisionCaseRequired(final Xnf xnf, final Sort sort, final RelationSymbol relSymb) {
		return SmtSortUtils.isIntSort(sort) && ((relSymb == RelationSymbol.DISTINCT) && xnf == Xnf.DNF
				|| (relSymb == RelationSymbol.EQ) && xnf == Xnf.CNF);
	}

	static SupportingTerm constructDerIntegerDivisionSupportingTerm(final Script script,
			final Term intLiteralDivConstraint) {
		final SupportingTerm result = new SupportingTerm(intLiteralDivConstraint,
				IntricateOperation.DIV_BY_INTEGER_CONSTANT, Collections.emptySet());
		return result;
	}

	/**
	 * TODO: (1) Documentation (2) Max has an optimization for nested mod terms with similar divisor, maybe we should
	 * simplify such terms in advance or here
	 *
	 * @param xnf
	 * @param bannedForDivCapture
	 * @param term
	 *
	 */
	private static MultiCaseSolvedBinaryRelation findTreatableDivModSubterm(final ManagedScript mgdScript, final Term subject,
			final IPolynomialTerm divident, final ApplicationTerm parentDivModTerm, final Xnf xnf,
			final Term relationInPnf, final Set<TermVariable> bannedForDivCapture) {
		for (final Monomial m : divident.getMonomial2Coefficient().keySet()) {
			for (final Term abstractVariable : m.getVariable2Exponent().keySet()) {
				if (SmtUtils.isIntDiv(abstractVariable) || SmtUtils.isIntMod(abstractVariable)) {
					final ApplicationTerm appTerm = (ApplicationTerm) abstractVariable;
					if (appTerm.getParameters().length > 2) {
						throw new UnsupportedOperationException("Div with more than two parameters");
					}
					final boolean dividentContainsSubject = SmtUtils.isSubterm(appTerm.getParameters()[0], subject);
					final boolean tailIsConstant = tailIsConstant(Arrays.asList(appTerm.getParameters()));
					if (dividentContainsSubject) {
						final IPolynomialTerm innerDivident = (IPolynomialTerm) new PolynomialTermTransformer(mgdScript.getScript())
								.transform(appTerm.getParameters()[0]);
						final ApplicationTerm suiteableDivModParent;
						if (tailIsConstant) {
							suiteableDivModParent = appTerm;
						} else {
							suiteableDivModParent = null;
						}
						final MultiCaseSolvedBinaryRelation rec = findTreatableDivModSubterm(mgdScript, subject,
								innerDivident, suiteableDivModParent, xnf, relationInPnf, bannedForDivCapture);
						if (rec != null) {
							return rec;
						}
					}
				}
			}
		}
		if (parentDivModTerm == null) {
			return null;
		}
		return tryToHandleDivModSubterm(mgdScript, subject, xnf, parentDivModTerm, relationInPnf, bannedForDivCapture);
	}

	public static boolean isVariableDivCaptured(final SolvedBinaryRelation sbr, final Set<TermVariable> termVariables) {
		if (sbr.getIntricateOperation().contains(IntricateOperation.DIV_BY_INTEGER_CONSTANT)) {
			final Term term = sbr.getRightHandSide();
			return someGivenTermVariableOccursInTerm(term, termVariables);
		}
		return false;
	}

	@Deprecated
	private static boolean someGivenTermVariableOccursInTerm(final Term term, final Set<TermVariable> termVariables) {
		final Set<ApplicationTerm> divSubterms = SmtUtils.extractApplicationTerms("div", term, false);
		return divSubterms.stream().anyMatch(x -> Arrays.stream(x.getFreeVars()).anyMatch(termVariables::contains));
	}

	public static boolean isVariableDivCaptured(final MultiCaseSolvedBinaryRelation mcsbr,
			final Set<TermVariable> termVariables) {
		if (mcsbr.getIntricateOperations().contains(IntricateOperation.DIV_BY_INTEGER_CONSTANT)) {
			for (final Case c : mcsbr.getCases()) {
				if (c.getSolvedBinaryRelation() != null && someGivenTermVariableOccursInTerm(
						c.getSolvedBinaryRelation().getRightHandSide(), termVariables)) {
					return true;
				}
				for (final SupportingTerm st : c.getSupportingTerms()) {
					if (st.getIntricateOperation() == IntricateOperation.DIV_BY_INTEGER_CONSTANT
							&& Arrays.stream(st.getTerm().getFreeVars()).anyMatch(termVariables::contains)) {
						return true;
					}
				}
			}
		}
		return false;
	}

}
