package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.logic.INonSolverScript;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.BinaryRelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.util.VMUtils;

public abstract class AbstractGeneralizedaAffineRelation {

	protected static final String NO_AFFINE_REPRESENTATION_WHERE_DESIRED_VARIABLE_IS_ON_LEFT_HAND_SIDE = "No affine representation where desired variable is on left hand side";
	protected static final boolean TEMPORARY_POLYNOMIAL_TERM_TEST = false;
	protected final Term mOriginalTerm;
	protected final RelationSymbol mRelationSymbol;
	protected final TrivialityStatus mTrivialityStatus;
	/**
	 * Affine term ψ such that the relation ψ ▷ 0 is equivalent to the
	 * mOriginalTerm.
	 *
	 */
	protected final AffineTerm mAffineTerm;

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
	public AbstractGeneralizedaAffineRelation(final Script script, final AffineTerm term, final RelationSymbol relationSymbol) {
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

	/**
	 * Transform {@link Term} to {@link AffineRelation} without transforming any
	 * equalities (i.e., by keeping the original relation of the term).
	 *
	 * @param term
	 * @throws NotAffineException
	 */
//	public AbstractGeneralizedaAffineRelation(final Script script, final Term term) throws NotAffineException {
//		this(script, term, TransformInequality.NO_TRANFORMATION);
//	}

//	/**
//	 * Transform Term into AffineRelation.
//	 *
//	 * @param term
//	 *            Term to which the resulting AffineRelation is equivalent.
//	 * @param transformInequality
//	 *            transform strict inequalities to non-strict inequalities and vice
//	 *            versa
//	 * @throws NotAffineException
//	 *             Thrown if Term is not affine.
//	 */
//	public AbstractGeneralizedaAffineRelation(final Script script, final Term term, final TransformInequality transformInequality)
//			throws NotAffineException {
//		mOriginalTerm = term;
//		final BinaryNumericRelation bnr = BinaryNumericRelation.convert(term);
//		if (bnr == null) {
//			throw new NotAffineException("Relation is not affine");
//		}
//
//		final Term lhs = bnr.getLhs();
//		final Term rhs = bnr.getRhs();
//		final AffineTerm affineLhs = transformToAffineTerm(script, lhs);
//		final AffineTerm affineRhs = transformToAffineTerm(script, rhs);
//		if (affineLhs.isErrorTerm() || affineRhs.isErrorTerm()) {
//			throw new NotAffineException("Relation is not affine");
//		}
//		final AffineTerm difference = AffineTerm.sum(affineLhs, AffineTerm.mul(affineRhs, Rational.MONE));
//		if (transformInequality != TransformInequality.NO_TRANFORMATION
//				&& SmtSortUtils.isIntSort(difference.getSort())) {
//			if (transformInequality == TransformInequality.STRICT2NONSTRICT) {
//				switch (bnr.getRelationSymbol()) {
//				case DISTINCT:
//				case EQ:
//				case GEQ:
//				case LEQ:
//					// relation symbol is not strict anyway
//					mAffineTerm = difference;
//					mRelationSymbol = bnr.getRelationSymbol();
//					break;
//				case LESS:
//					// increment affine term by one
//					mRelationSymbol = RelationSymbol.LEQ;
//					mAffineTerm = AffineTerm.sum(difference,
//							AffineTerm.constructConstant(difference.getSort(), Rational.ONE));
//					break;
//				case GREATER:
//					// decrement affine term by one
//					mRelationSymbol = RelationSymbol.GEQ;
//					mAffineTerm = AffineTerm.sum(difference,
//							AffineTerm.constructConstant(difference.getSort(), Rational.MONE));
//
//					break;
//				default:
//					throw new AssertionError("unknown symbol");
//				}
//			} else if (transformInequality == TransformInequality.NONSTRICT2STRICT) {
//				switch (bnr.getRelationSymbol()) {
//				case DISTINCT:
//				case EQ:
//				case LESS:
//				case GREATER:
//					// relation symbol is strict anyway
//					mAffineTerm = difference;
//					mRelationSymbol = bnr.getRelationSymbol();
//					break;
//				case GEQ:
//					// increment affine term by one
//					mRelationSymbol = RelationSymbol.GREATER;
//					mAffineTerm = AffineTerm.sum(difference,
//							AffineTerm.constructConstant(difference.getSort(), Rational.ONE));
//					break;
//				case LEQ:
//					// decrement affine term by one
//					mRelationSymbol = RelationSymbol.LESS;
//					mAffineTerm = AffineTerm.sum(difference,
//							AffineTerm.constructConstant(difference.getSort(), Rational.MONE));
//					break;
//				default:
//					throw new AssertionError("unknown symbol");
//				}
//			} else {
//				throw new AssertionError("unknown case");
//			}
//		} else {
//			mAffineTerm = difference;
//			mRelationSymbol = bnr.getRelationSymbol();
//		}
//		mTrivialityStatus = computeTrivialityStatus(mAffineTerm, mRelationSymbol);
//	}

	protected AbstractGeneralizedaAffineRelation(final Script script, final TransformInequality transformInequality,
			final RelationSymbol relationSymbol, final AffineTerm affineLhs, final AffineTerm affineRhs, final Term originalTerm) {
		mOriginalTerm = originalTerm;
		final AffineTerm difference = AffineTerm.sum(affineLhs, AffineTerm.mul(affineRhs, Rational.MONE));
		final AffineTerm affineTerm;
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
					affineTerm = AffineTerm.sum(difference,
							AffineTerm.constructConstant(difference.getSort(), Rational.ONE));
					break;
				case GREATER:
					// decrement affine term by one
					relationSymbolAfterTransformation = RelationSymbol.GEQ;
					affineTerm = AffineTerm.sum(difference,
							AffineTerm.constructConstant(difference.getSort(), Rational.MONE));
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
					affineTerm = AffineTerm.sum(difference,
							AffineTerm.constructConstant(difference.getSort(), Rational.ONE));
					break;
				case LEQ:
					// decrement affine term by one
					relationSymbolAfterTransformation = RelationSymbol.LESS;
					affineTerm = AffineTerm.sum(difference,
							AffineTerm.constructConstant(difference.getSort(), Rational.MONE));
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
//		return new AbstractGeneralizedaAffineRelation(script, affineTerm, relationSymbolAfterTransformation);
	}

	protected abstract AffineTerm sum(final AffineTerm op1, final AffineTerm op2);

	protected abstract AffineTerm mul(final AffineTerm op, final Rational r);

	protected abstract AffineTerm constructConstant(final Sort s, final Rational r);

	protected static final TrivialityStatus computeTrivialityStatus(final AffineTerm term, final RelationSymbol symbol) {
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

	private static TrivialityStatus computeTrivialityStatus(final AffineTerm term, final Predicate<Integer> pred) {
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
			for (final Entry<Term, Rational> entry : mAffineTerm.getVariable2Coefficient().entrySet()) {
				if (entry.getValue().isNegative()) {
					rhsSummands.add(product(script, entry.getValue().abs(), entry.getKey()));
				} else {
					lhsSummands.add(product(script, entry.getValue(), entry.getKey()));
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



	public AffineTerm getAffineTerm() {
		return mAffineTerm;
	}

}