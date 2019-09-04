package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.BinaryRelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.SolvedBinaryRelation.AssumptionForSolvability;
import de.uni_freiburg.informatik.ultimate.logic.INonSolverScript;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.util.VMUtils;

public abstract class AbstractGeneralizedaAffineRelation<AGAT extends AbstractGeneralizedAffineTerm<AVAR>, AVAR extends Term>
		implements IBinaryRelation {

	protected static final String NO_AFFINE_REPRESENTATION_WHERE_DESIRED_VARIABLE_IS_ON_LEFT_HAND_SIDE = "No affine representation where desired variable is on left hand side";
	protected static final boolean TEMPORARY_POLYNOMIAL_TERM_TEST = false;
	private static final boolean THROW_EXCEPTION_IF_NOT_SOLVABLE = false;
	protected final Term mOriginalTerm;
	protected final RelationSymbol mRelationSymbol;
	protected final TrivialityStatus mTrivialityStatus;
	/**
	 * Affine term ψ such that the relation ψ ▷ 0 is equivalent to the
	 * mOriginalTerm.
	 */
	protected final AGAT mAffineTerm;

	public enum TransformInequality {
		NO_TRANFORMATION, STRICT2NONSTRICT, NONSTRICT2STRICT
	}

	public enum TrivialityStatus {
		EQUIVALENT_TO_TRUE, EQUIVALENT_TO_FALSE, NONTRIVIAL
	}

	/**
	 * Create {@link AffineRelation} from {@link AffineTerm} and
	 * {@link RelationSymbol}.
	 *
	 * Resulting relation is then <code><term> <symbol> 0</code>.
	 */
	public AbstractGeneralizedaAffineRelation(final Script script, final AGAT term,
			final RelationSymbol relationSymbol) {
		mAffineTerm = Objects.requireNonNull(term);
		mRelationSymbol = relationSymbol;

		mTrivialityStatus = computeTrivialityStatus(mAffineTerm, mRelationSymbol);
		if (VMUtils.areAssertionsEnabled()) {
			mOriginalTerm = script.term(mRelationSymbol.toString(), term.toTerm(script),
					SmtUtils.constructIntegerValue(script, term.getSort(), BigInteger.ZERO));
		} else {
			mOriginalTerm = null;
		}
	}

	protected AbstractGeneralizedaAffineRelation(final Script script, final TransformInequality transformInequality,
			final RelationSymbol relationSymbol, final AGAT affineLhs, final AGAT affineRhs, final Term originalTerm) {
		mOriginalTerm = originalTerm;
		final AGAT difference = sum(affineLhs, mul(affineRhs, Rational.MONE));
		final AGAT affineTerm;
		final RelationSymbol relationSymbolAfterTransformation;

		if (transformInequality != TransformInequality.NO_TRANFORMATION
				&& SmtSortUtils.isIntSort(difference.getSort())) {
			if (transformInequality == TransformInequality.STRICT2NONSTRICT) {
				switch (relationSymbol) {
				case DISTINCT:
				case EQ:
				case GEQ:
				case LEQ:
					// relation symbol is not strict anyway
					affineTerm = difference;
					relationSymbolAfterTransformation = relationSymbol;
					break;
				case LESS:
					// increment affine term by one
					relationSymbolAfterTransformation = RelationSymbol.LEQ;
					affineTerm = sum(difference, constructConstant(difference.getSort(), Rational.ONE));
					break;
				case GREATER:
					// decrement affine term by one
					relationSymbolAfterTransformation = RelationSymbol.GEQ;
					affineTerm = sum(difference, constructConstant(difference.getSort(), Rational.MONE));
					break;
				default:
					throw new AssertionError("unknown symbol");
				}
			} else if (transformInequality == TransformInequality.NONSTRICT2STRICT) {
				switch (relationSymbol) {
				case DISTINCT:
				case EQ:
				case LESS:
				case GREATER:
					// relation symbol is strict anyway
					affineTerm = difference;
					relationSymbolAfterTransformation = relationSymbol;
					break;
				case GEQ:
					// increment affine term by one
					relationSymbolAfterTransformation = RelationSymbol.GREATER;
					affineTerm = sum(difference, constructConstant(difference.getSort(), Rational.ONE));
					break;
				case LEQ:
					// decrement affine term by one
					relationSymbolAfterTransformation = RelationSymbol.LESS;
					affineTerm = sum(difference, constructConstant(difference.getSort(), Rational.MONE));
					break;
				default:
					throw new AssertionError("unknown symbol");
				}
			} else {
				throw new AssertionError("unknown case");
			}
		} else {
			affineTerm = difference;
			relationSymbolAfterTransformation = relationSymbol;
		}
		mAffineTerm = affineTerm;
		mRelationSymbol = relationSymbolAfterTransformation;
		mTrivialityStatus = computeTrivialityStatus(affineTerm, relationSymbolAfterTransformation);
		// return new AbstractGeneralizedaAffineRelation(script, affineTerm,
		// relationSymbolAfterTransformation);
	}

	protected abstract AGAT sum(final AGAT op1, final AGAT op2);

	protected abstract AGAT mul(final AGAT op, final Rational r);

	protected abstract AGAT constructConstant(final Sort s, final Rational r);

	/**
	 * Check if subject occurs in exactly one abstract variable. Assumes that
	 * subject is variable of at least one abstract variable (throws AssertionError
	 * otherwise). Returns null if subject occurs in more that one abstract
	 * variable, returns the abstract variable of the subject otherwise.
	 */
	protected abstract AVAR getTheAbstractVarOfSubject(final Term subject);

	protected static <AGAT extends AbstractGeneralizedAffineTerm<?>> TrivialityStatus computeTrivialityStatus(
			final AGAT term, final RelationSymbol symbol) {
		if (!term.isConstant()) {
			return TrivialityStatus.NONTRIVIAL;
		}

		switch (symbol) {
		case DISTINCT:
			return computeTrivialityStatus(term, a -> a != 0);
		case EQ:
			return computeTrivialityStatus(term, a -> a == 0);
		case LESS:
			return computeTrivialityStatus(term, a -> a < 0);
		case GREATER:
			return computeTrivialityStatus(term, a -> a > 0);
		case GEQ:
			return computeTrivialityStatus(term, a -> a >= 0);
		case LEQ:
			return computeTrivialityStatus(term, a -> a <= 0);
		default:
			throw new UnsupportedOperationException("unknown relation symbol: " + symbol);
		}
	}

	private static <AGAT extends AbstractGeneralizedAffineTerm<?>> TrivialityStatus computeTrivialityStatus(
			final AGAT term, final Predicate<Integer> pred) {
		if (pred.test(term.getConstant().signum())) {
			return TrivialityStatus.EQUIVALENT_TO_TRUE;
		}
		return TrivialityStatus.EQUIVALENT_TO_FALSE;
	}

	protected static LBool isEquivalent(final Script script, final Term term1, final Term term2) {
		Term comp = script.term("=", term1, term2);
		comp = script.term("not", comp);
		final LBool sat = Util.checkSat(script, comp);
		return sat;
	}

	protected static LBool assumptionImpliesEquivalence(final Script script, final Term originalTerm,
			final Term relationToTerm, final Term additionalAssumption) {
		final Term impli1 = SmtUtils.implies(script, additionalAssumption, relationToTerm);
		final Term impli2 = SmtUtils.implies(script, additionalAssumption, originalTerm);
		return isEquivalent(script, impli1, impli2);
	}

	public RelationSymbol getRelationSymbol() {
		return mRelationSymbol;
	}

	/**
	 * @return true iff var is variable of this {@link AffineRelation}
	 */
	public boolean isVariable(final Term var) {
		return mAffineTerm.isVariable(var);
	}

	/**
	 * Returns a term representation of this AffineRelation where each summand
	 * occurs only positive and the greater-than relation symbols are replaced by
	 * less-than relation symbols. If the term is equivalent to <i>true</i> (resp.
	 * <i>false</i>) we return <i>true</i> (resp. <i>false</i>).
	 */
	public Term positiveNormalForm(final Script script) {
		if (mTrivialityStatus == TrivialityStatus.EQUIVALENT_TO_TRUE) {
			return script.term("true");
		} else if (mTrivialityStatus == TrivialityStatus.EQUIVALENT_TO_FALSE) {
			return script.term("false");
		} else {
			assert mTrivialityStatus == TrivialityStatus.NONTRIVIAL;
			final List<Term> lhsSummands = new ArrayList<>();
			final List<Term> rhsSummands = new ArrayList<>();
			for (final Entry<AVAR, Rational> entry : mAffineTerm.getAbstractVariable2Coefficient().entrySet()) {
				final Term abstractVariableAsTerm = mAffineTerm.abstractVariableToTerm(script, entry.getKey());
				if (entry.getValue().isNegative()) {
					rhsSummands.add(product(script, entry.getValue().abs(), abstractVariableAsTerm));
				} else {
					lhsSummands.add(product(script, entry.getValue(), abstractVariableAsTerm));
				}
			}
			if (mAffineTerm.getConstant() != Rational.ZERO) {
				if (mAffineTerm.getConstant().isNegative()) {
					rhsSummands.add(
							SmtUtils.rational2Term(script, mAffineTerm.getConstant().abs(), mAffineTerm.getSort()));
				} else {
					lhsSummands.add(SmtUtils.rational2Term(script, mAffineTerm.getConstant(), mAffineTerm.getSort()));
				}
			}
			final Term lhsTerm = SmtUtils.sum(script, mAffineTerm.getSort(),
					lhsSummands.toArray(new Term[lhsSummands.size()]));
			final Term rhsTerm = SmtUtils.sum(script, mAffineTerm.getSort(),
					rhsSummands.toArray(new Term[rhsSummands.size()]));
			final Term result = BinaryRelation.constructLessNormalForm(script, mRelationSymbol, lhsTerm, rhsTerm);
			assert script instanceof INonSolverScript || isEquivalent(script, mOriginalTerm,
					result) != LBool.SAT : "transformation to positive normal form " + "unsound";
			return result;
		}
	}

	protected static Term product(final Script script, final Rational rational, final Term term) {
		if (rational.equals(Rational.ONE)) {
			return term;
		} else if (rational.equals(Rational.MONE)) {
			return SmtUtils.neg(script, term);
		} else {
			final Term coefficient = SmtUtils.rational2Term(script, rational, term.getSort());
			return SmtUtils.mul(script, term.getSort(), coefficient, term);
		}
	}

	public AGAT getAffineTerm() {
		return mAffineTerm;
	}

	/**
	 * Returns a {@link SolvedBinaryRelation} that is equivalent to this
	 * PolynomialRelation or null if we cannot find such a
	 * {@link SolvedBinaryRelation}.
	 */
	@Override
	public SolvedBinaryRelation solveForSubject(final Script script, final Term subject) {
		if (!isVariable(subject)) {
			if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
				throw new UnsupportedOperationException("subject is not a variable");
			} else {
				return null;
			}
		}
		final AVAR abstractVarOfSubject = getTheAbstractVarOfSubject(subject);
		if (abstractVarOfSubject == null) {
			if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
				throw new UnsupportedOperationException("subject occurs in several abstract variables");
			} else {
				return null;
			}
		}
		final Rational coeffOfSubject = mAffineTerm.getAbstractVariable2Coefficient().get(abstractVarOfSubject);
		if (coeffOfSubject.equals(Rational.ZERO)) {
			throw new AssertionError("no abstract variable must have coefficient zero");
		}
		if (SmtSortUtils.isBitvecSort(mAffineTerm.getSort()) && !coeffOfSubject.abs().equals(Rational.ONE)) {
			// for bitvectors we may only divide by 1 or -1
			// reason: consider bitvectors of length 8 (i.e., 256=0)
			// then e.g., 2*x = 0 is not equivalent to x = 0 because
			// for x=128 the first equation hold but the second does not
			if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
				throw new UnsupportedOperationException(
						"for bitvector subjects only coefficients 1 and -1 are supported");
			} else {
				return null;
			}
		}

		final Term assumptionFreeRhsTerm = constructRhsForAbstractVariable(script, abstractVarOfSubject,
				coeffOfSubject);
		Map<AssumptionForSolvability, Term> assumptionsMap = Collections.emptyMap();
		Term rhsTerm;
		if (assumptionFreeRhsTerm == null) {
			final Term rhsTermWithoutDivision = constructRhsForAbstractVariable(script, abstractVarOfSubject,
					Rational.ONE);
			rhsTerm = integerDivision(script, coeffOfSubject, rhsTermWithoutDivision);
			// EQ and DISTINCT need Modulo Assumption
			if ((mRelationSymbol.equals(RelationSymbol.EQ)) || (mRelationSymbol.equals(RelationSymbol.DISTINCT))) {
				Term modTerm = SmtUtils.mod(script, rhsTermWithoutDivision,
						coeffOfSubject.toTerm(mAffineTerm.getSort()));
				modTerm = SmtUtils.binaryEquality(script, modTerm, TermParseUtils.parseTerm(script, "0"));
				assumptionsMap = Collections.singletonMap(AssumptionForSolvability.INTEGER_DIVISIBLE_BY_CONSTANT,
						modTerm);
			}
		} else {
			rhsTerm = assumptionFreeRhsTerm;
		}

		final RelationSymbol resultRelationSymbol;
		if (coeffOfSubject.isNegative()) {
			// if coefficient is negative we have to use the "swapped" RelationSymbol
			resultRelationSymbol = BinaryRelation.swapParameters(mRelationSymbol);
		} else {
			resultRelationSymbol = mRelationSymbol;
		}

		// TODO 2019-06-10 Matthias:
		// Add here some code for polynominals where we have to try to divide by the
		// other variables in the monomial

		final SolvedBinaryRelation result = new SolvedBinaryRelation(subject, rhsTerm, resultRelationSymbol,
				assumptionsMap);
		final Term relationToTerm = result.relationToTerm(script);
		if (!assumptionsMap.isEmpty()) {
			assert script instanceof INonSolverScript
					|| assumptionImpliesEquivalence(script, mOriginalTerm, relationToTerm, assumptionsMap.entrySet()
							.iterator().next().getValue()) != LBool.SAT : "transformation to AffineRelation unsound";
		} else {
			assert script instanceof INonSolverScript || isEquivalent(script, mOriginalTerm,
					relationToTerm) != LBool.SAT : "transformation to AffineRelation unsound";
		}
		return result;
	}

	private Term integerDivision(final Script script, final Rational coeffOfSubject,
			final Term rhsTermWithoutDivision) {
		// Default DivTerm
		Term divTerm = SmtUtils.div(script, rhsTermWithoutDivision, coeffOfSubject.toTerm(mAffineTerm.getSort()));
		// change DivTerm according to the given relation symbol
		switch (mRelationSymbol) {
		case LESS:
			// k*x < t is equivalent to x < (t-1 div k)+1 for positive k
			if (!coeffOfSubject.isNegative()) {
				divTerm = constructDivTerm(script, rhsTermWithoutDivision, coeffOfSubject, Rational.ONE);
			} else if (coeffOfSubject.isNegative()) {
				// -k*x >= t is equivalent to x <= (t - 1 div -k) - 1
				divTerm = constructDivTerm(script, rhsTermWithoutDivision, coeffOfSubject, Rational.MONE);
			}
			break;
		case GREATER:
			// k*x > t is equivalent to x > (t div k) for all k
			break;
		case LEQ:
			// k*x <= t is equivalent to x <= (t div k) for positive k
			break;
		case GEQ:
			// k*x >= t is equivalent to x >= (t - 1 div k) + 1 for positive k
			if (!coeffOfSubject.isNegative()) {
				divTerm = constructDivTerm(script, rhsTermWithoutDivision, coeffOfSubject, Rational.ONE);
			} else if (coeffOfSubject.isNegative()) {
				// -k*x >= t is equivalent to x <= (t - 1 div -k) - 1
				divTerm = constructDivTerm(script, rhsTermWithoutDivision, coeffOfSubject, Rational.MONE);
			}
			break;
		case EQ:
			// Default DivTerm with modulo Assumption
			break;
		case DISTINCT:
			// Default DivTerm with modulo Assumption
			break;
		default:
			throw new AssertionError("unknown relation symbol: " + mRelationSymbol);
		}
		return divTerm;
	}

	/*
	 * construct DivTerm for LESS and GEQ case, where the default divTerm can't be
	 * used. "secondRat" depends on the sign of the coefficient.
	 */
	private Term constructDivTerm(final Script script, Term rhsTermWithoutDivision, final Rational coeffOfSubject,
			final Rational secondRat) {
		rhsTermWithoutDivision = SmtUtils.sum(script, mAffineTerm.getSort(), rhsTermWithoutDivision,
				SmtUtils.rational2Term(script, Rational.MONE, mAffineTerm.getSort()));
		final Term divTerm = SmtUtils.div(script, rhsTermWithoutDivision, coeffOfSubject.toTerm(mAffineTerm.getSort()));
		return SmtUtils.sum(script, mAffineTerm.getSort(), divTerm,
				SmtUtils.rational2Term(script, secondRat, mAffineTerm.getSort()));
	}

	/**
	 * Try to bring everything but abstractVarOfSubject to the right-hand side. Try
	 * to divide the coefficient of every other variable and the constant by the
	 * coeffOfAbstractVar. If the sort is not real and for some coefficient the
	 * quotient is not integral return null. Otherwise return the {@link Term}
	 * representation of the right-hand side.
	 */
	private Term constructRhsForAbstractVariable(final Script script, final AVAR abstractVarOfSubject,
			final Rational coeffOfAbstractVar) {
		final List<Term> rhsSummands = new ArrayList<>(mAffineTerm.getAbstractVariable2Coefficient().size());
		for (final Entry<AVAR, Rational> entry : mAffineTerm.getAbstractVariable2Coefficient().entrySet()) {
			if (abstractVarOfSubject == entry.getKey()) {
				// do nothing
			} else {
				final Rational newCoeff = entry.getValue().div(coeffOfAbstractVar);
				if (newCoeff.isIntegral() || SmtSortUtils.isRealSort(mAffineTerm.getSort())) {
					rhsSummands.add(product(script, newCoeff.negate(), entry.getKey()));
				} else {
					if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
						throw new UnsupportedOperationException(
								"some coefficient not divisible by coefficient of subject");
					} else {
						return null;
					}
				}
			}
		}
		if (!mAffineTerm.getConstant().equals(Rational.ZERO)) {
			final Rational newConstant = mAffineTerm.getConstant().div(coeffOfAbstractVar);
			if (newConstant.isIntegral() || SmtSortUtils.isRealSort(mAffineTerm.getSort())) {
				rhsSummands.add(SmtUtils.rational2Term(script, newConstant.negate(), mAffineTerm.getSort()));
			} else {
				if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
					throw new UnsupportedOperationException("some constant not divisible by coefficient of subject");
				} else {
					return null;
				}
			}
		}
		final Term rhsTerm = SmtUtils.sum(script, mAffineTerm.getSort(),
				rhsSummands.toArray(new Term[rhsSummands.size()]));
		return rhsTerm;
	}

}