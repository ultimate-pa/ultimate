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
import java.util.List;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryNumericRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.IBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.logic.INonSolverScript;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.VMUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Represents an term of the form ψ ▷ φ, where ψ and φ are {@link PolynomialTerm}s or {@link AffineTerm}s and ▷ is a
 * binary relation symbol from the following list.
 * <p>
 * ▷ ∈ { =, !=, \<=, \<, \>=, \> }
 * </p>
 * <p>
 * Allows to return this relation as an SMT term in the following two forms:
 * <ul>
 * <li>positive normal form
 * <li>the form where a specific variable is on the left hand side and all other summands are moved to the right hand
 * side.
 * </ul>
 * </p>
 *
 * @author Leonard Fichtner
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class PolynomialRelation implements IBinaryRelation {

	protected static final String NO_AFFINE_REPRESENTATION_WHERE_DESIRED_VARIABLE_IS_ON_LEFT_HAND_SIDE =
			"No affine representation where desired variable is on left hand side";
	protected static final boolean TEMPORARY_POLYNOMIAL_TERM_TEST = false;
	protected final Term mOriginalTerm;
	protected final RelationSymbol mRelationSymbol;
	protected final TrivialityStatus mTrivialityStatus;
	/**
	 * Affine term ψ such that the relation ψ ▷ 0 is equivalent to the mOriginalTerm.
	 */
	protected final AbstractGeneralizedAffineTerm<Term> mPolynomialTerm;

	public enum TransformInequality {
		NO_TRANFORMATION, STRICT2NONSTRICT, NONSTRICT2STRICT
	}

	public enum TrivialityStatus {
		EQUIVALENT_TO_TRUE, EQUIVALENT_TO_FALSE, NONTRIVIAL
	}

	/**
	 * Create {@link PolynomialRelation} from {@link IPolynomialTerm} and {@link RelationSymbol}.
	 *
	 * Resulting relation is then <code><term> <symbol> 0</code>.
	 *
	 * @deprecated no constructor for this special case
	 */
	@Deprecated
	public PolynomialRelation(final Script script, final AbstractGeneralizedAffineTerm<?> term,
			final RelationSymbol relationSymbol) {
		mPolynomialTerm = Objects.requireNonNull(checkThenCast(term));
		mRelationSymbol = relationSymbol;

		mTrivialityStatus = computeTrivialityStatus(mPolynomialTerm, mRelationSymbol);
		if (VMUtils.areAssertionsEnabled()) {
			mOriginalTerm = script.term(mRelationSymbol.toString(), term.toTerm(script),
					SmtUtils.constructIntegerValue(script, term.getSort(), BigInteger.ZERO));
		} else {
			mOriginalTerm = null;
		}
	}

	public PolynomialRelation(final Script script, final TransformInequality transformInequality,
			final RelationSymbol relationSymbol, final AbstractGeneralizedAffineTerm<?> polyLhs,
			final AbstractGeneralizedAffineTerm<?> polyRhs, final Term originalTerm) {
		mOriginalTerm = originalTerm;
		final AbstractGeneralizedAffineTerm<Term> difference =
				sum(checkThenCast(polyLhs), mul(checkThenCast(polyRhs), Rational.MONE));
		final AbstractGeneralizedAffineTerm<Term> polyTerm;
		final RelationSymbol relationSymbolAfterTransformation;

		if (transformInequality != TransformInequality.NO_TRANFORMATION
				&& SmtSortUtils.isIntSort(difference.getSort())) {
			if (transformInequality == TransformInequality.STRICT2NONSTRICT) {
				switch (relationSymbol) {
				case DISTINCT:
				case EQ:
				case GEQ:
				case BVULE:
				case BVUGE:
				case BVSLE:
				case BVSGE:
				case LEQ:
					// relation symbol is not strict anyway
					polyTerm = difference;
					relationSymbolAfterTransformation = relationSymbol;
					break;
				case LESS:
					// increment polynomial term by one
					relationSymbolAfterTransformation = RelationSymbol.LEQ;
					polyTerm = sum(difference, constructConstant(difference.getSort(), Rational.ONE));
					break;
				case GREATER:
					// decrement polynomial term by one
					relationSymbolAfterTransformation = RelationSymbol.GEQ;
					polyTerm = sum(difference, constructConstant(difference.getSort(), Rational.MONE));
					break;
				case BVULT:
				case BVUGT:
				case BVSLT:
				case BVSGT:
					throw new AssertionError("STRICT2NONSTRICT for Bitvector not implemented");
				default:
					throw new AssertionError("unknown symbol");
				}
			} else if (transformInequality == TransformInequality.NONSTRICT2STRICT) {
				switch (relationSymbol) {
				case DISTINCT:
				case EQ:
				case BVULT:
				case BVUGT:
				case BVSLT:
				case BVSGT:
				case LESS:
				case GREATER:
					// relation symbol is strict anyway
					polyTerm = difference;
					relationSymbolAfterTransformation = relationSymbol;
					break;
				case GEQ:
					// increment polynomial term by one
					relationSymbolAfterTransformation = RelationSymbol.GREATER;
					polyTerm = sum(difference, constructConstant(difference.getSort(), Rational.ONE));
					break;
				case LEQ:
					// decrement polynomial term by one
					relationSymbolAfterTransformation = RelationSymbol.LESS;
					polyTerm = sum(difference, constructConstant(difference.getSort(), Rational.MONE));
					break;
				case BVULE:
				case BVUGE:
				case BVSLE:
				case BVSGE:
					throw new AssertionError("NONSTRICT2STRICT for Bitvector not implemented");
				default:
					throw new AssertionError("unknown symbol");
				}
			} else {
				throw new AssertionError("unknown case");
			}
		} else {
			polyTerm = difference;
			relationSymbolAfterTransformation = relationSymbol;
		}
		mPolynomialTerm = polyTerm;
		mRelationSymbol = relationSymbolAfterTransformation;
		mTrivialityStatus = computeTrivialityStatus(polyTerm, relationSymbolAfterTransformation);
	}

	private AbstractGeneralizedAffineTerm<Term> sum(final AbstractGeneralizedAffineTerm<Term> op1,
			final AbstractGeneralizedAffineTerm<Term> op2) {
		final AbstractGeneralizedAffineTerm<Term> result;
		if (op1.isAffine() && op2.isAffine()) {
			result = AffineTerm.sum(op1, op2);
		} else {
			final AbstractGeneralizedAffineTerm<?> polynomialSum = PolynomialTerm.sum(op1, op2);
			result = unsafeCast(polynomialSum);
		}
		return result;
	}

	private AbstractGeneralizedAffineTerm<Term> mul(final AbstractGeneralizedAffineTerm<Term> op, final Rational r) {
		final AbstractGeneralizedAffineTerm<Term> result;
		if (op.isAffine()) {
			result = AffineTerm.mul(op, r);
		} else {
			final AbstractGeneralizedAffineTerm<?> polynomialSum = PolynomialTerm.mul(op, r);
			result = unsafeCast(polynomialSum);
		}
		return result;
	}

	private AffineTerm constructConstant(final Sort s, final Rational r) {
		return AffineTerm.constructConstant(s, r);
	}

	/**
	 * Given a AbstractGeneralizedAffineTerm, check whether it is of Type AffineTerm and PolynomialTerm. If yes, cast it
	 * (UNSAFE) and return the result, throw an exception otherwise.
	 */
	private static AbstractGeneralizedAffineTerm<Term> checkThenCast(final AbstractGeneralizedAffineTerm<?> poly) {
		if (!(poly instanceof AffineTerm || poly instanceof PolynomialTerm)) {
			throw new IllegalArgumentException(
					"PolynomialRelation accepts only AffineTerm " + "and PolynomialTerm as internal terms.");
		}
		return unsafeCast(poly);
	}

	@SuppressWarnings("unchecked")
	private static AbstractGeneralizedAffineTerm<Term> unsafeCast(final AbstractGeneralizedAffineTerm<?> poly) {
		return (AbstractGeneralizedAffineTerm<Term>) poly;
	}

	private static TrivialityStatus computeTrivialityStatus(final AbstractGeneralizedAffineTerm<Term> term,
			final RelationSymbol symbol) {
		if (!term.isConstant()) {
			return checkMinMaxValues(term, symbol);
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
		case BVULE:
		case BVULT:
		case BVUGE:
		case BVUGT:
		case BVSLE:
		case BVSLT:
		case BVSGE:
		case BVSGT:
			return TrivialityStatus.NONTRIVIAL;
		default:
			throw new UnsupportedOperationException("unknown relation symbol: " + symbol);
		}
	}

	private static TrivialityStatus checkMinMaxValues(final AbstractGeneralizedAffineTerm<Term> term,
			final RelationSymbol symbol) {
		final Pair<Rational, Rational> minMaxValues = term.computeMinMax();
		final TrivialityStatus result;
		if (minMaxValues == null) {
			result = TrivialityStatus.NONTRIVIAL;
		} else {
			final Rational minimalValue = minMaxValues.getFirst();
			final Rational maximalValue = minMaxValues.getSecond();
			switch (symbol) {
			case DISTINCT:
				if (minimalValue.compareTo(Rational.ZERO) > 0 || maximalValue.compareTo(Rational.ZERO) < 0) {
					result = TrivialityStatus.EQUIVALENT_TO_TRUE;
				} else {
					result = TrivialityStatus.NONTRIVIAL;
				}
				break;
			case EQ:
				if (minimalValue.compareTo(Rational.ZERO) > 0 || maximalValue.compareTo(Rational.ZERO) < 0) {
					result = TrivialityStatus.EQUIVALENT_TO_FALSE;
				} else {
					result = TrivialityStatus.NONTRIVIAL;
				}
				break;
			case LESS:
				if (maximalValue.compareTo(Rational.ZERO) < 0) {
					result = TrivialityStatus.EQUIVALENT_TO_TRUE;
				} else if (minimalValue.compareTo(Rational.ZERO) >= 0) {
					result = TrivialityStatus.EQUIVALENT_TO_FALSE;
				} else {
					result = TrivialityStatus.NONTRIVIAL;
				}
				break;
			case GREATER:
				if (minimalValue.compareTo(Rational.ZERO) > 0) {
					result = TrivialityStatus.EQUIVALENT_TO_TRUE;
				} else if (maximalValue.compareTo(Rational.ZERO) <= 0) {
					result = TrivialityStatus.EQUIVALENT_TO_FALSE;
				} else {
					result = TrivialityStatus.NONTRIVIAL;
				}
				break;
			case GEQ:
				if (minimalValue.compareTo(Rational.ZERO) >= 0) {
					result = TrivialityStatus.EQUIVALENT_TO_TRUE;
				} else if (maximalValue.compareTo(Rational.ZERO) < 0) {
					result = TrivialityStatus.EQUIVALENT_TO_FALSE;
				} else {
					result = TrivialityStatus.NONTRIVIAL;
				}
				break;
			case LEQ:
				if (maximalValue.compareTo(Rational.ZERO) <= 0) {
					result = TrivialityStatus.EQUIVALENT_TO_TRUE;
				} else if (minimalValue.compareTo(Rational.ZERO) > 0) {
					result = TrivialityStatus.EQUIVALENT_TO_FALSE;
				} else {
					result = TrivialityStatus.NONTRIVIAL;
				}
				break;
			case BVULE:
			case BVULT:
			case BVUGE:
			case BVUGT:
			case BVSLE:
			case BVSLT:
			case BVSGE:
			case BVSGT:
				result = TrivialityStatus.NONTRIVIAL;
			default:
				throw new UnsupportedOperationException("unknown relation symbol: " + symbol);
			}
		}
		return result;
	}

	private static TrivialityStatus computeTrivialityStatus(final AbstractGeneralizedAffineTerm<Term> term,
			final Predicate<Integer> pred) {
		if (pred.test(term.getConstant().signum())) {
			return TrivialityStatus.EQUIVALENT_TO_TRUE;
		} else {
			return TrivialityStatus.EQUIVALENT_TO_FALSE;
		}
	}

	public RelationSymbol getRelationSymbol() {
		return mRelationSymbol;
	}

	public AbstractGeneralizedAffineTerm<Term> getPolynomialTerm() {
		return mPolynomialTerm;
	}

	/**
	 * Returns a term representation of this PolynomialRelation where each summand occurs only positive and the
	 * greater-than relation symbols are replaced by less-than relation symbols. If the term is equivalent to
	 * <i>true</i> (resp. <i>false</i>) we return <i>true</i> (resp. <i>false</i>).
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
			for (final Entry<Term, Rational> entry : mPolynomialTerm.getAbstractVariable2Coefficient().entrySet()) {
				final Term abstractVariableAsTerm = mPolynomialTerm.abstractVariableToTerm(script, entry.getKey());
				if (entry.getValue().isNegative()) {
					rhsSummands.add(SmtUtils.mul(script, entry.getValue().abs(), abstractVariableAsTerm));
				} else {
					lhsSummands.add(SmtUtils.mul(script, entry.getValue(), abstractVariableAsTerm));
				}
			}
			if (mPolynomialTerm.getConstant() != Rational.ZERO) {
				if (mPolynomialTerm.getConstant().isNegative()) {
					rhsSummands.add(SmtUtils.rational2Term(script, mPolynomialTerm.getConstant().abs(),
							mPolynomialTerm.getSort()));
				} else {
					lhsSummands.add(
							SmtUtils.rational2Term(script, mPolynomialTerm.getConstant(), mPolynomialTerm.getSort()));
				}
			}
			final Term lhsTerm =
					SmtUtils.sum(script, mPolynomialTerm.getSort(), lhsSummands.toArray(new Term[lhsSummands.size()]));
			final Term rhsTerm =
					SmtUtils.sum(script, mPolynomialTerm.getSort(), rhsSummands.toArray(new Term[rhsSummands.size()]));
			final Term result = BinaryRelation.constructLessNormalForm(script, mRelationSymbol, lhsTerm, rhsTerm);
			assert script instanceof INonSolverScript || SmtUtils.checkEquivalence(mOriginalTerm, result,
					script) != LBool.SAT : "transformation to positive normal form " + "unsound";
			return result;
		}
	}

	/**
	 * Returns a {@link SolvedBinaryRelation} that is equivalent to this PolynomialRelation or null if we cannot find
	 * such a {@link SolvedBinaryRelation}.
	 */
	@Override
	public SolvedBinaryRelation solveForSubject(final Script script, final Term subject) {
		final ExplicitLhsPolynomialRelation elpr =
				ExplicitLhsPolynomialRelation.moveMonomialToLhs(script, subject, this);
		if (elpr == null) {
			return null;
		} else {
			if (!elpr.getLhsMonomial().isLinear()) {
				return null;
			}
			final ExplicitLhsPolynomialRelation solvedElpr = elpr.divInvertible(elpr.getLhsCoefficient());
			if (solvedElpr == null) {
				return null;
			} else {
				assert subject.equals(solvedElpr.getLhsMonomial().getSingleVariable());
				final SolvedBinaryRelation result = new SolvedBinaryRelation(subject,
						solvedElpr.getRhs().toTerm(script), solvedElpr.getRelationSymbol());
				final Term relationToTerm = result.asTerm(script);
				assert script instanceof INonSolverScript || SmtUtils.checkEquivalence(positiveNormalForm(script),
						relationToTerm, script) != LBool.SAT : "solveForSubject unsound";
				return result;
			}
		}
	}

	/**
	 * Returns a {@link MultiCaseSolvedBinaryRelation} that is equivalent to this PolynomialRelation or null if we
	 * cannot find such a {@link MultiCaseSolvedBinaryRelation}.
	 */
	public MultiCaseSolvedBinaryRelation solveForSubject(final Script script, final Term subject,
			final MultiCaseSolvedBinaryRelation.Xnf xnf, final Set<TermVariable> bannedForDivCapture) {
		return SolveForSubjectUtils.solveForSubject(script, subject, xnf, this, bannedForDivCapture);
	}

	/**
	 * @return true iff the relation ψ ▷ φ has (after simplification) a form where ψ and φ are both affine terms.
	 */
	public boolean isAffine() {
		return mPolynomialTerm.isAffine();
	}

	/**
	 * @return true iff var is variable of this {@link PolynomialRelation}
	 */
	public boolean isVariable(final Term var) {
		return mPolynomialTerm.isVariable(var);
	}

	public static PolynomialRelation convert(final Script script, final Term term) {
		return convert(script, term, TransformInequality.NO_TRANFORMATION);
	}

	public static PolynomialRelation convert(final Script script, final Term term,
			final TransformInequality transformInequality) {
		final BinaryNumericRelation bnr = BinaryNumericRelation.convert(term);
		if (bnr == null) {
			return null;
		}
		final Term lhs = bnr.getLhs();
		final Term rhs = bnr.getRhs();
		final AbstractGeneralizedAffineTerm<?> polyLhs = transformToPolynomialTerm(script, lhs);
		final AbstractGeneralizedAffineTerm<?> polyRhs = transformToPolynomialTerm(script, rhs);
		if (polyLhs.isErrorTerm() || polyRhs.isErrorTerm()) {
			return null;
		}
		if (bnr.getRelationSymbol().isConvexInequality() && SmtSortUtils.isBitvecSort(lhs.getSort())) {
			return null;
		}
		final RelationSymbol relationSymbol = bnr.getRelationSymbol();
		return new PolynomialRelation(script, transformInequality, relationSymbol, polyLhs, polyRhs, term);
	}

	static AbstractGeneralizedAffineTerm<?> transformToPolynomialTerm(final Script script, final Term term) {
		return (AbstractGeneralizedAffineTerm<?>) new PolynomialTermTransformer(script).transform(term);
	}
}