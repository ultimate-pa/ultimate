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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ITermProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.IBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.MultiCaseSolvedBinaryRelation.IntricateOperation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.MultiCaseSolvedBinaryRelation.Xnf;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation.TransformInequality;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.XnfTir;
import de.uni_freiburg.informatik.ultimate.logic.INonSolverScript;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Polynomial relation in which we explicitly state which {@link Monomial} (together with its coefficient) is on the
 * left-hand side. This class is used as an intermediate data structure by algorithms that try to solve a polynomial
 * relation for a given subject.
 *
 * <pre>
 * Work in progress.
 * * Maybe we want to allow more general right-hand sides.
 * * Maybe we do not only want to solve relations (coefficient one) but
 *     want to do transformations whose result has a specific coefficient.
 * </pre>
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class ExplicitLhsPolynomialRelation implements IBinaryRelation, ITermProvider {

	private static final boolean THROW_EXCEPTION_IF_NOT_SOLVABLE = false;

	protected final RelationSymbol mRelationSymbol;
	protected final Rational mLhsCoefficient;
	protected final Monomial mLhsMonomial;
	protected final IPolynomialTerm mRhs;

	public ExplicitLhsPolynomialRelation(final RelationSymbol relationSymbol, final Rational lhsCoefficient,
			final Monomial lhsMonomial, final IPolynomialTerm rhs) {
		super();
		mRelationSymbol = relationSymbol;
		mLhsCoefficient = lhsCoefficient;
		mLhsMonomial = lhsMonomial;
		mRhs = rhs;
	}

	public RelationSymbol getRelationSymbol() {
		return mRelationSymbol;
	}

	public Rational getLhsCoefficient() {
		return mLhsCoefficient;
	}

	public Monomial getLhsMonomial() {
		return mLhsMonomial;
	}

	public IPolynomialTerm getRhs() {
		return mRhs;
	}

	public ExplicitLhsPolynomialRelation changeRelationSymbol(final RelationSymbol relationSymbol) {
		return new ExplicitLhsPolynomialRelation(relationSymbol, mLhsCoefficient, mLhsMonomial, mRhs);
	}

	public static ExplicitLhsPolynomialRelation moveMonomialToLhs(final Script script, final Term subject,
			final PolynomialRelation polyRel) {

		final Monomial monomialOfSubject = polyRel.getPolynomialTerm().getExclusiveMonomialOfSubject(subject);
		if (monomialOfSubject == null) {
			if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
				throw new UnsupportedOperationException("subject is not exclusive variables");
			} else {
				return null;
			}
		}
		if (monomialOfSubject.getVariable2Exponent().get(subject) != Rational.ONE) {
			if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
				throw new UnsupportedOperationException("roots not yet supported");
			} else {
				return null;
			}
		}
		final Rational coeffOfSubject;
		if (polyRel.getPolynomialTerm().isAffine()) {
			final Term singleVariable = monomialOfSubject.getSingleVariable();
			assert subject.equals(singleVariable);
			coeffOfSubject = polyRel.getPolynomialTerm().getAbstractVariable2Coefficient().get(singleVariable);
		} else {
			coeffOfSubject = polyRel.getPolynomialTerm().getAbstractVariable2Coefficient().get(monomialOfSubject);
		}
		if (coeffOfSubject.equals(Rational.ZERO)) {
			throw new AssertionError("no abstract variable must have coefficient zero");
		}

		return new ExplicitLhsPolynomialRelation(polyRel.getRelationSymbol(), coeffOfSubject, monomialOfSubject,
				polyRel.getPolynomialTerm().removeAndNegate(monomialOfSubject));
	}

	/**
	 * @deprecated We do not have an application for this method yet. I was
	 *             developed at a time where we wrongly assumed that the following
	 *             transformation is sound `∃x. lo<=2x /\ 2x<=hi` ~~~> `lo<=hi`
	 */
	@Deprecated
	public ExplicitLhsPolynomialRelation mul(final Rational factor, final Script script, final boolean tight) {
		if (factor.equals(Rational.ZERO)) {
			throw new AssertionError("mul by zero not supported");
		}
		final Rational newLhsCoefficient = mLhsCoefficient.mul(factor);
		final RelationSymbol resultRelationSymbol =
				determineResultRelationSymbol(mLhsMonomial.getSort(), mRelationSymbol, factor);
		final IPolynomialTerm newRhs;
		if (tight && (resultRelationSymbol.equals(RelationSymbol.LESS)
				|| resultRelationSymbol.equals(RelationSymbol.GREATER))) {
			final Rational offsetAbs;
			if (resultRelationSymbol.equals(RelationSymbol.LESS)) {
				offsetAbs = factor.abs().add(Rational.MONE).negate();
			} else {
				assert resultRelationSymbol.equals(RelationSymbol.GREATER);
				offsetAbs = factor.abs().add(Rational.MONE);
			}
			newRhs = PolynomialTermOperations.sum(PolynomialTermOperations.mul(mRhs, factor),
					new AffineTerm(mLhsMonomial.getSort(), offsetAbs, Collections.emptyMap()));
		} else if (!tight && (resultRelationSymbol.equals(RelationSymbol.LEQ)
				|| resultRelationSymbol.equals(RelationSymbol.GEQ))) {
			final Rational offsetAbs;
			if (resultRelationSymbol.equals(RelationSymbol.GEQ)) {
				offsetAbs = factor.abs().add(Rational.MONE).negate();
			} else {
				assert resultRelationSymbol.equals(RelationSymbol.LEQ);
				offsetAbs = factor.abs().add(Rational.MONE);
			}
			newRhs = PolynomialTermOperations.sum(PolynomialTermOperations.mul(mRhs, factor),
					new AffineTerm(mLhsMonomial.getSort(), offsetAbs, Collections.emptyMap()));
		} else {
			newRhs = PolynomialTermOperations.mul(mRhs, factor);
		}
		final ExplicitLhsPolynomialRelation result =
				new ExplicitLhsPolynomialRelation(resultRelationSymbol, newLhsCoefficient, mLhsMonomial, newRhs);
		assert script instanceof INonSolverScript || SmtUtils.checkEquivalence(toTerm(script), result.toTerm(script),
				script) != LBool.SAT : "mul unsound";
		return result;
	}

	/**
	 * Divide both sides of the relation by a {@link Rational} such the resulting
	 * relation is logically equivalent, has the same monomials (i.e., each `div`
	 * term can be resolved), and there is an inverse operation (multiplication)
	 * that yields the original relation. <br>
	 * This method has a special behavior for inequalities that have Int sort. It is
	 * applicable even if the constant of the polynomial is not divisible by this
	 * method's divisor, because we do a transformation that is based on the
	 * following equalities for positive k.
	 * <li> `k*x <= t` iff `x <= t div k`
	 * <li> `k*x < t` iff `x < ((t-1) div k) +1`
	 * <li> `k*x => t` iff `x => ((t-1) div k) +1`
	 * <li> `k*x => t` iff `x => t div k`
	 *
	 */
	public ExplicitLhsPolynomialRelation divInvertible(final Rational divisor) {
		if (divisor.equals(Rational.ZERO)) {
			throw new AssertionError("div by zero");
		}
		final RelationSymbol resultRelationSymbol =
				determineResultRelationSymbol(mLhsMonomial.getSort(), mRelationSymbol, divisor);
		final IPolynomialTerm newRhs;
		if (resultRelationSymbol.isConvexInequality() && SmtSortUtils.isIntSort(mRhs.getSort())) {
			final IPolynomialTerm rhsWithoutConst = mRhs.add(mRhs.getConstant().negate());
			assert rhsWithoutConst.getConstant().equals(Rational.ZERO);
			final IPolynomialTerm newRhsWithoutConst = rhsWithoutConst.divInvertible(divisor);
			if (newRhsWithoutConst == null) {
				return null;
			}
			final Rational constWithRightSign;
			if (divisor.isNegative()) {
				constWithRightSign = mRhs.getConstant().negate();
			} else {
				constWithRightSign = mRhs.getConstant();
			}
			final Rational newConst;
			if (resultRelationSymbol.equals(RelationSymbol.LEQ) || resultRelationSymbol.equals(RelationSymbol.GREATER)) {
				newConst = constWithRightSign.div(divisor.abs()).floor();
			} else if (resultRelationSymbol.equals(RelationSymbol.LESS) || resultRelationSymbol.equals(RelationSymbol.GEQ) ) {
				newConst = constWithRightSign.add(Rational.MONE).div(divisor.abs()).floor().add(Rational.ONE);
			} else {
				throw new AssertionError("Unexpected relation symbol: " + resultRelationSymbol);
			}
			newRhs = newRhsWithoutConst.add(newConst);
		} else {
			newRhs = mRhs.divInvertible(divisor);
		}
		if (newRhs == null) {
			return null;
		}
		final Rational newLhsCoefficient =
				PolynomialTermUtils.divInvertible(mLhsMonomial.getSort(), mLhsCoefficient, divisor);
		if (newLhsCoefficient == null) {
			return null;
		}
		return new ExplicitLhsPolynomialRelation(resultRelationSymbol, newLhsCoefficient, mLhsMonomial, newRhs);
	}

	private RelationSymbol determineResultRelationSymbol(final Sort sort, final RelationSymbol relationSymbol,
			final Rational divisor) {
		final RelationSymbol resultRelationSymbol =
				swapOfRelationSymbolRequired(divisor, sort) ? relationSymbol.swapParameters() : relationSymbol;
		return resultRelationSymbol;
	}

	public static boolean swapOfRelationSymbolRequired(final Rational divisor, final Sort sort) {
		return divisor.isNegative() || (SmtSortUtils.isBitvecSort(sort) && SmtUtils.isBvMinusOneButNotOne(divisor, sort));
	}

	public Pair<ExplicitLhsPolynomialRelation, Term> divideByIntegerCoefficient(final Script script,
			final Set<TermVariable> bannedForDivCapture) {
		if (mLhsCoefficient.equals(Rational.ZERO)) {
			throw new AssertionError("div by zero");
		}
		if (!SmtSortUtils.isIntSort(mLhsMonomial.getSort())) {
			throw new AssertionError("no int: " + mLhsMonomial.getSort());
		}
		final Term divisor = mLhsCoefficient.toTerm(mLhsMonomial.getSort());
		final IPolynomialTerm resultRhs = SolveForSubjectUtils.constructRhsIntegerQuotient(script, mRelationSymbol,
				mRhs, !mLhsCoefficient.isNegative(), divisor, bannedForDivCapture);
		final Term rhsAsTerm = mRhs.toTerm(script);
		if (resultRhs == null) {
			assert (Arrays.stream(rhsAsTerm.getFreeVars())
					.anyMatch(bannedForDivCapture::contains)) : "no ban problem detected";
			return null;
		}
		final Term divisibilityConstraint;
		switch (mRelationSymbol) {
		case DISTINCT:
			divisibilityConstraint = constructDivisibilityConstraint(script, true, rhsAsTerm, divisor);
			break;
		case EQ:
			divisibilityConstraint = constructDivisibilityConstraint(script, false, rhsAsTerm, divisor);
			break;
		case GEQ:
		case GREATER:
		case LEQ:
		case LESS:
		case BVULE:
		case BVULT:
		case BVUGE:
		case BVUGT:
		case BVSLE:
		case BVSLT:
		case BVSGE:
		case BVSGT:
			divisibilityConstraint = null;
			break;
		default:
			throw new AssertionError("unknown value " + mRelationSymbol);
		}
		final RelationSymbol resultRelationSymbol = determineResultRelationSymbol(mLhsMonomial.getSort(),
				mRelationSymbol, mLhsCoefficient);
		final ExplicitLhsPolynomialRelation resultElpr = new ExplicitLhsPolynomialRelation(resultRelationSymbol,
				Rational.ONE, getLhsMonomial(), resultRhs);
		return new Pair<>(resultElpr, divisibilityConstraint);
	}

	/**
	 * @deprecated Only called by the old {@link XnfTir} class.
	 */
	@Deprecated
	public SolvedBinaryRelation divideByIntegerCoefficientForInequalities(final Script script,
			final Set<TermVariable> bannedForDivCapture) {
		switch (mRelationSymbol) {
		case DISTINCT:
		case EQ:
			throw new AssertionError("no inequality");
		case GEQ:
		case GREATER:
		case LEQ:
		case LESS:
		case BVULE:
		case BVULT:
		case BVUGE:
		case BVUGT:
		case BVSLE:
		case BVSLT:
		case BVSGE:
		case BVSGT:
			break;
		default:
			throw new AssertionError("unknown value " + mRelationSymbol);
		}
		final Pair<ExplicitLhsPolynomialRelation, Term> tmp = divideByIntegerCoefficient(script, bannedForDivCapture);
		if (tmp == null) {
			return null;
		}
		assert (tmp.getSecond() == null);
		final ExplicitLhsPolynomialRelation resultElpr = tmp.getFirst();
		return new SolvedBinaryRelation(mLhsMonomial.getSingleVariable(), resultElpr.getRhs().toTerm(script),
				resultElpr.getRelationSymbol(), IntricateOperation.DIV_BY_INTEGER_CONSTANT);
	}

	public MultiCaseSolvedBinaryRelation divByMonomial(final Script script, final Term subject, final Xnf xnf,
			final Set<TermVariable> bannedForDivCapture, final Term intLiteralDivConstraint,
			final IntricateOperation additionalIo) {
		if (!mLhsCoefficient.equals(Rational.ONE)) {
			throw new AssertionError("could be supported, but should not be used in our applications");
		}
		final Term rhs = mRhs.toTerm(script);
		if (mLhsMonomial.isLinear()) {
			throw new AssertionError("division not necessary");
		}
		if (Arrays.stream(rhs.getFreeVars()).anyMatch(bannedForDivCapture::contains)) {
			return null;
		}
		final EnumSet<IntricateOperation> intricateOperations;
		if (additionalIo == null) {
			intricateOperations = EnumSet.of(IntricateOperation.DIV_BY_NONCONSTANT);
		} else {
			intricateOperations = EnumSet.of(IntricateOperation.DIV_BY_NONCONSTANT, additionalIo);
		}
		final MultiCaseSolutionBuilder mcsb = new MultiCaseSolutionBuilder(subject, xnf);
		final Collection<Case> cases = new ArrayList<>();
		// TODO 13.11.2019 Leonard: When we divide by variables we could actually
		// sometimes simplify the resulting division, in the case that this variable is
		// not zero (and therefore we can simplify f.ex. x/x to 1). Also we could
		// sometimes get conjuncts like x!=0, that are already in the case distinction.
		// Handle this in the MultiCaseSolutionBuilder?
		// At the moment this seems like much work relative to little effect, so I was
		// asked to leave this comment here for the future.
		final List<Term> twoCaseVariables = new ArrayList<>();
		final Set<SupportingTerm> distinctZeroSupportingTerms = new HashSet<>();
		final List<Term> threeCaseVariables = new ArrayList<>();
		final List<SupportingTerm> isNegativeSupportingTerms = new ArrayList<>();
		final List<SupportingTerm> isPositiveSupportingTerms = new ArrayList<>();
		final List<Term> factorsOfDivisor = new ArrayList<>();
		for (final Entry<Term, Rational> var2exp : mLhsMonomial.getVariable2Exponent().entrySet()) {
			assert var2exp.getValue().isIntegral();
			if (var2exp.getKey() == subject) {
				// do nothing
			} else {
				cases.add(constructDivByVarEqualZeroCase(script, var2exp.getKey(), rhs, mRelationSymbol, xnf,
						intLiteralDivConstraint));
				final int exp = var2exp.getValue().numerator().intValueExact();
				for (int i = 0; i < exp; i++) {
					factorsOfDivisor.add(var2exp.getKey());
				}
				if (isEqOrDistinct(mRelationSymbol) || exp % 2 == 0) {
					twoCaseVariables.add(var2exp.getKey());
					distinctZeroSupportingTerms.add(constructInRelationToZeroSupportingTerm(script, var2exp.getKey(),
							SolveForSubjectUtils.negateForCnf(RelationSymbol.DISTINCT, xnf)));
				} else {
					// We have to distinguish the case now into two cases,
					// since the RelationSymbol has to be swapped, when we divide by a negative
					// variable.
					threeCaseVariables.add(var2exp.getKey());
					isNegativeSupportingTerms.add(constructInRelationToZeroSupportingTerm(script, var2exp.getKey(),
							SolveForSubjectUtils.negateForCnf(RelationSymbol.LESS, xnf)));
					isPositiveSupportingTerms.add(constructInRelationToZeroSupportingTerm(script, var2exp.getKey(),
							SolveForSubjectUtils.negateForCnf(RelationSymbol.GREATER, xnf)));
				}
			}
		}
		final Term divisor = SmtUtils.mul(script, factorsOfDivisor.get(0).getSort(),
				factorsOfDivisor.toArray(new Term[factorsOfDivisor.size()]));
		if (threeCaseVariables.isEmpty()) {
			final SolvedBinaryRelation sbr = constructSolvedBinaryRelation(script, subject, mRhs, mRelationSymbol, true,
					divisor, intricateOperations, bannedForDivCapture);
			final Set<SupportingTerm> thisCaseSupportingTerms = new HashSet<>(distinctZeroSupportingTerms);
			if (SolveForSubjectUtils.isDerIntegerDivisionSupportingTermRequired(xnf, subject.getSort(),
					mRelationSymbol)) {
				final SupportingTerm divisibilityConstraintMonomial = constructDerIntegerDivisionSupportingTerm(script,
						rhs, mRelationSymbol, divisor);
				thisCaseSupportingTerms.add(divisibilityConstraintMonomial);
				if (intLiteralDivConstraint != null) {
					final SupportingTerm divisibilityConstraintLiteral = SolveForSubjectUtils
							.constructDerIntegerDivisionSupportingTerm(script, intLiteralDivConstraint);
					thisCaseSupportingTerms.add(divisibilityConstraintLiteral);
				}
			}
			cases.add(new Case(sbr, thisCaseSupportingTerms, xnf));
		} else {
			if (threeCaseVariables.size() > 30) {
				throw new UnsupportedOperationException(
						"Exponential blowup too huge. Exponent is " + threeCaseVariables.size());
			}
			final int numberOfCases = BigInteger.valueOf(2).pow(threeCaseVariables.size()).intValueExact();
			for (int i = 0; i < numberOfCases; i++) {
				// if bit is set this means that we assume that variable is negative
				final boolean isDivisorPositive = ((BigInteger.valueOf(i).bitCount() % 2 == 0));
				final SolvedBinaryRelation sbr = constructSolvedBinaryRelation(script, subject, mRhs, mRelationSymbol,
						isDivisorPositive, divisor, intricateOperations, bannedForDivCapture);
				final Set<SupportingTerm> thisCaseSupportingTerms = new HashSet<>(distinctZeroSupportingTerms);
				for (int j = 0; j < threeCaseVariables.size(); j++) {
					SupportingTerm posOrNegSupportingTerm;
					if (BigInteger.valueOf(i).testBit(j)) {
						posOrNegSupportingTerm = isNegativeSupportingTerms.get(j);
					} else {
						posOrNegSupportingTerm = isPositiveSupportingTerms.get(j);
					}
					thisCaseSupportingTerms.add(posOrNegSupportingTerm);
				}
				if (SolveForSubjectUtils.isDerIntegerDivisionSupportingTermRequired(xnf, subject.getSort(),
						mRelationSymbol)) {
					final SupportingTerm divisibilityConstraint = constructDerIntegerDivisionSupportingTerm(script, rhs,
							mRelationSymbol, divisor);
					thisCaseSupportingTerms.add(divisibilityConstraint);
					assert intLiteralDivConstraint != null;
					final SupportingTerm divisibilityConstraintLiteral = SolveForSubjectUtils
							.constructDerIntegerDivisionSupportingTerm(script, intLiteralDivConstraint);
					thisCaseSupportingTerms.add(divisibilityConstraintLiteral);

				}
				cases.add(new Case(sbr, thisCaseSupportingTerms, xnf));
			}
		}
		if (SolveForSubjectUtils.isAntiDerIntegerDivisionCaseRequired(xnf, subject.getSort(), mRelationSymbol)) {
			final Case result = constructAntiDerIntegerDivisibilityCase(script, xnf, rhs, mRelationSymbol, divisor);
			cases.add(result);
			if (intLiteralDivConstraint != null) {
				final SupportingTerm intLiteralDivConstraintSuppTerm = new SupportingTerm(intLiteralDivConstraint,
						IntricateOperation.DIV_BY_INTEGER_CONSTANT, Collections.emptySet());
				final Case caseForLiteral = new Case(null, Collections.singleton(intLiteralDivConstraintSuppTerm), xnf);
				cases.add(caseForLiteral);
			}
		}
		mcsb.splitCases(cases);

		final MultiCaseSolvedBinaryRelation result = mcsb.buildResult();
		return result;
	}

	private static SupportingTerm constructDerIntegerDivisionSupportingTerm(final Script script, final Term stageTwoRhs,
			final RelationSymbol relSymb, final Term divisor) {
		final boolean negate = relSymb.equals(RelationSymbol.DISTINCT);
		final Term divisibilityConstraintTerm = constructDivisibilityConstraint(script, negate, stageTwoRhs,
				SmtUtils.mul(script, stageTwoRhs.getSort(), divisor));
		final SupportingTerm divisibilityConstraint = new SupportingTerm(divisibilityConstraintTerm,
				IntricateOperation.DIV_BY_NONCONSTANT, Collections.emptySet());
		return divisibilityConstraint;
	}

	private static Case constructAntiDerIntegerDivisibilityCase(final Script script,
			final MultiCaseSolvedBinaryRelation.Xnf xnf, final Term stageTwoRhs, final RelationSymbol relSymb,
			final Term divisorAsArray) {
		final Set<SupportingTerm> suppTerms = new HashSet<>();
		final boolean negate = relSymb.equals(RelationSymbol.DISTINCT);
		final Term divisibilityConstraintTerm = constructDivisibilityConstraint(script, negate, stageTwoRhs,
				SmtUtils.mul(script, stageTwoRhs.getSort(), divisorAsArray));
		final SupportingTerm divisibilityConstraint = new SupportingTerm(divisibilityConstraintTerm,
				IntricateOperation.DIV_BY_NONCONSTANT, Collections.emptySet());
		suppTerms.add(divisibilityConstraint);

		final SupportingTerm inRelationToZero = constructInRelationToZeroSupportingTerm(script,
				SmtUtils.mul(script, stageTwoRhs.getSort(), divisorAsArray),
				SolveForSubjectUtils.negateForCnf(RelationSymbol.DISTINCT, xnf));
		suppTerms.add(inRelationToZero);
		final Case result = new Case(null, suppTerms, xnf);
		return result;
	}

	private static SupportingTerm constructInRelationToZeroSupportingTerm(final Script script, final Term term,
			final RelationSymbol relSym) {
		final Term zero = SmtUtils.rational2Term(script, Rational.ZERO, term.getSort());
		final Term termRelZero = relSym.constructTerm(script, term, zero);
		return new SupportingTerm(termRelZero, IntricateOperation.DIV_BY_NONCONSTANT, Collections.emptySet());
	}

	private static SolvedBinaryRelation constructSolvedBinaryRelation(final Script script, final Term subject,
			final IPolynomialTerm rhs, final RelationSymbol relSymb, final boolean isDivisorPositive,
			final Term divisor, final EnumSet<IntricateOperation> intricateOperations,
			final Set<TermVariable> bannedForDivCapture) {
		final RelationSymbol resultRelationSymbol;
		if (isDivisorPositive) {
			resultRelationSymbol = relSymb;
		} else {
			// if coefficient is negative we have to use the "swapped" RelationSymbol
			resultRelationSymbol = relSymb.swapParameters();
		}
		final Term resultRhs;
		if (SmtSortUtils.isIntSort(rhs.getSort())) {
			resultRhs = SolveForSubjectUtils
					.constructRhsIntegerQuotient(script, relSymb, rhs, isDivisorPositive, divisor, bannedForDivCapture)
					.toTerm(script);
			if (resultRhs == null) {
				return null;
			}
		} else {
			resultRhs = SmtUtils.divReal(script, SolveForSubjectUtils.prepend(rhs.toTerm(script), divisor));
		}
		final SolvedBinaryRelation sbr = new SolvedBinaryRelation(subject, resultRhs, resultRelationSymbol,
				intricateOperations.toArray(new IntricateOperation[intricateOperations.size()]));
		return sbr;
	}

	public static Term constructDivisibilityConstraint(final Script script, final boolean negate, final Term divident,
			final Term divisor) {
		final Term modTerm = SmtUtils.mod(script, divident, divisor);
		final Term tmp = SmtUtils.binaryEquality(script, modTerm,
				SmtUtils.constructIntegerValue(script, SmtSortUtils.getIntSort(script), BigInteger.ZERO));
		final Term result;
		if (negate) {
			result = SmtUtils.not(script, tmp);
		} else {
			result = tmp;
		}
		return result;
	}

	private static Case constructDivByVarEqualZeroCase(final Script script, final Term divisorVar, final Term rhs,
			final RelationSymbol relSym, final Xnf xnf, final Term intLiteralDivConstraint) {
		final Set<SupportingTerm> suppTerms = new LinkedHashSet<>();
		if (SolveForSubjectUtils.isDerIntegerDivisionSupportingTermRequired(xnf, divisorVar.getSort(), relSym)
				&& intLiteralDivConstraint != null) {
			suppTerms.add(
					SolveForSubjectUtils.constructDerIntegerDivisionSupportingTerm(script, intLiteralDivConstraint));
		}
		final Term zeroTerm = SmtUtils.rational2Term(script, Rational.ZERO, divisorVar.getSort());
		final Term varEqualZero = SmtUtils.binaryEquality(script, zeroTerm, divisorVar);
		final SupportingTerm st;
		switch (xnf) {
		case CNF:
			st = new SupportingTerm(SmtUtils.not(script, varEqualZero), IntricateOperation.DIV_BY_NONCONSTANT,
					Collections.emptySet());
			break;
		case DNF:
			st = new SupportingTerm(varEqualZero, IntricateOperation.DIV_BY_NONCONSTANT, Collections.emptySet());
			break;
		default:
			throw new AssertionError("unknown value " + xnf);
		}
		suppTerms.add(st);
		final Term rhsRelationZeroTerm;
		switch (relSym) {
		case EQ:
			rhsRelationZeroTerm = SmtUtils.binaryEquality(script, zeroTerm, rhs);
			break;
		case DISTINCT:
			rhsRelationZeroTerm = SmtUtils.distinct(script, zeroTerm, rhs);
			break;
		case LEQ:
			rhsRelationZeroTerm = SmtUtils.leq(script, zeroTerm, rhs);
			break;
		case LESS:
			rhsRelationZeroTerm = SmtUtils.less(script, zeroTerm, rhs);
			break;
		case GEQ:
			rhsRelationZeroTerm = SmtUtils.geq(script, zeroTerm, rhs);
			break;
		case GREATER:
			rhsRelationZeroTerm = SmtUtils.greater(script, zeroTerm, rhs);
			break;
		case BVULE:
			rhsRelationZeroTerm = SmtUtils.bvule(script, zeroTerm, rhs);
			break;
		case BVULT:
			rhsRelationZeroTerm = SmtUtils.bvult(script, zeroTerm, rhs);
			break;
		case BVUGE:
			rhsRelationZeroTerm = SmtUtils.bvuge(script, zeroTerm, rhs);
			break;
		case BVUGT:
			rhsRelationZeroTerm = SmtUtils.bvugt(script, zeroTerm, rhs);
			break;
		case BVSLE:
			rhsRelationZeroTerm = SmtUtils.bvsle(script, zeroTerm, rhs);
			break;
		case BVSLT:
			rhsRelationZeroTerm = SmtUtils.bvslt(script, zeroTerm, rhs);
			break;
		case BVSGE:
			rhsRelationZeroTerm = SmtUtils.bvsge(script, zeroTerm, rhs);
			break;
		case BVSGT:
			rhsRelationZeroTerm = SmtUtils.bvsgt(script, zeroTerm, rhs);
			break;
		default:
			throw new AssertionError("Unknown RelationSymbol: " + relSym);
		}
		suppTerms.add(
				new SupportingTerm(rhsRelationZeroTerm, IntricateOperation.DIV_BY_NONCONSTANT, Collections.emptySet()));
		return new Case(null, suppTerms, xnf);
	}

	public ExplicitLhsPolynomialRelation changeStrictness(final TransformInequality strictnessTrans) {
		if (!SmtSortUtils.isIntSort(mRhs.getSort())) {
			throw new UnsupportedOperationException("Change of strictness only for ints.");
		}
		if (strictnessTrans == TransformInequality.NO_TRANFORMATION) {
			return this;
		}
		switch (mRelationSymbol) {
		case EQ:
		case DISTINCT:
			throw new UnsupportedOperationException("Only applicable to integer inequalities");
		case BVSGE:
		case BVSGT:
		case BVSLE:
		case BVSLT:
		case BVUGE:
		case BVUGT:
		case BVULE:
		case BVULT:
			throw new UnsupportedOperationException("Only applicable to integer inequalities");
		case GEQ:
			if (strictnessTrans == TransformInequality.NONSTRICT2STRICT) {
				return new ExplicitLhsPolynomialRelation(RelationSymbol.GREATER, mLhsCoefficient, mLhsMonomial,
						mRhs.add(Rational.MONE));
			} else {
				throw new UnsupportedOperationException("Not strict");
			}
		case GREATER:
			if (strictnessTrans == TransformInequality.STRICT2NONSTRICT) {
				return new ExplicitLhsPolynomialRelation(RelationSymbol.GEQ, mLhsCoefficient, mLhsMonomial,
						mRhs.add(Rational.ONE));
			} else {
				throw new UnsupportedOperationException("Is strict");
			}
		case LEQ:
			if (strictnessTrans == TransformInequality.NONSTRICT2STRICT) {
				return new ExplicitLhsPolynomialRelation(RelationSymbol.LESS, mLhsCoefficient, mLhsMonomial,
						mRhs.add(Rational.ONE));
			} else {
				throw new UnsupportedOperationException("Not strict");
			}
		case LESS:
			if (strictnessTrans == TransformInequality.STRICT2NONSTRICT) {
				return new ExplicitLhsPolynomialRelation(RelationSymbol.LEQ, mLhsCoefficient, mLhsMonomial,
						mRhs.add(Rational.MONE));
			} else {
				throw new UnsupportedOperationException("Is strict");
			}
		default:
			throw new AssertionError("Unknown relation symbol " + mRelationSymbol);
		}
	}

	/**
	 * We call a {@link ExplicitLhsPolynomialRelation} tight if
	 * <li>the sort is Real and the lhs coefficient is 1.0 or if
	 * <li>the sort is Int and the lhs coefficient is positive and there is no
	 * equivalent {@link ExplicitLhsPolynomialRelation} that has a smaller lhs
	 * coefficient but the same monomials (i.e., it is not allowed to obtain the
	 * smaller lhs coefficient by a division that introduces a div term on the rhs).
	 * TODO 20230219 Matthias: Revise this documentation. Since the
	 * {@link PolynomialRelation} divides by the GCD the work that is done here can
	 * be explained more precisely.
	 */
	public ExplicitLhsPolynomialRelation makeTight() {
		Rational divisor;
		if (SmtSortUtils.isRealSort(mRhs.getSort())) {
			divisor = mLhsCoefficient;
		} else if (SmtSortUtils.isBitvecSort(mRhs.getSort())) {
			if (!mLhsCoefficient.equals(Rational.ONE)
					&& !SmtUtils.isBvMinusOneButNotOne(mLhsCoefficient, mRhs.getSort())) {
				throw new AssertionError("Expect that bitvector relations can only have coefficient 1 and -1.");
			}
			divisor = mLhsCoefficient;
		} else if (SmtSortUtils.isIntSort(mRhs.getSort())) {
			final Rational gcd = mLhsCoefficient.gcd(mRhs.computeGcdOfCoefficients()).abs();
			assert !gcd.isNegative();
			if (!gcd.equals(Rational.ONE)) {
				throw new AssertionError("The PolynomialRelation should have divided by the GCD!");
			}
			if (mLhsCoefficient.isNegative()) {
				divisor = gcd.negate();
			} else {
				divisor = gcd;
			}
		} else {
			throw new UnsupportedOperationException("Unsupported sort: " + mRhs.getSort());
		}
		if (divisor.equals(Rational.ONE)) {
			return this;
		}
		final ExplicitLhsPolynomialRelation res = divInvertible(divisor);
		if (res == null) {
			throw new AssertionError("Invertible division must not fail for " + divisor);
		}
		return res;
	}

	private static boolean isEqOrDistinct(final RelationSymbol relSym) {
		return (relSym.equals(RelationSymbol.EQ)) || (relSym.equals(RelationSymbol.DISTINCT));
	}

	@Override
	public SolvedBinaryRelation solveForSubject(final Script script, final Term subject) {
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public Term toTerm(final Script script) {
		final Term lhs = SmtUtils.mul(script, mLhsCoefficient, mLhsMonomial.toTerm(script));
		return mRelationSymbol.constructTerm(script, lhs, mRhs.toTerm(script));
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append(mLhsCoefficient);
		builder.append("*");
		builder.append(mLhsMonomial);
		builder.append(" ");
		builder.append(mRelationSymbol);
		builder.append(" ");
		builder.append(mRhs);
		return builder.toString();
	}

}
