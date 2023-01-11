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
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.BitvectorUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ITermProviderOnDemand;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryNumericRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.IBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.DualJunctionTir;
import de.uni_freiburg.informatik.ultimate.logic.INonSolverScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant;
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
public class PolynomialRelation implements IBinaryRelation, ITermProviderOnDemand {

	protected static final String NO_AFFINE_REPRESENTATION_WHERE_DESIRED_VARIABLE_IS_ON_LEFT_HAND_SIDE =
			"No affine representation where desired variable is on left hand side";
	protected static final boolean TEMPORARY_POLYNOMIAL_TERM_TEST = false;
	protected final RelationSymbol mRelationSymbol;
	protected final TrivialityStatus mTrivialityStatus;
	/**
	 * {@link PolynomialTerm}s or {@link AffineTerm}s ψ such that the relation ψ ▷ 0
	 * is equivalent to the mOriginalTerm.
	 */
	protected final AbstractGeneralizedAffineTerm<?> mPolynomialTerm;

	public enum TransformInequality {
		NO_TRANFORMATION, STRICT2NONSTRICT, NONSTRICT2STRICT;

		/**
		 * For the TIR quantifier elimination technique (see {@link DualJunctionTir}),
		 * we prefer non-strict inequalities for the existential quantifier and we
		 * prefer strict inequalities for the universal quantifier.
		 */
		public static TransformInequality determineTransformationForTir(final int quantifier) {
			TransformInequality result;
			if (quantifier == QuantifiedFormula.EXISTS) {
				result = TransformInequality.STRICT2NONSTRICT;
			} else if (quantifier == QuantifiedFormula.FORALL) {
				result = TransformInequality.NONSTRICT2STRICT;
			} else {
				throw new AssertionError("Unknown quantifier");
			}
			return result;
		}
	}

	public enum TrivialityStatus {
		EQUIVALENT_TO_TRUE, EQUIVALENT_TO_FALSE, NONTRIVIAL
	}

	/**
	 * Create {@link PolynomialRelation} from {@link IPolynomialTerm} and {@link RelationSymbol}.
	 *
	 * Resulting relation is then <code><term> <symbol> 0</code>.
	 *
	 */
	private PolynomialRelation(final AbstractGeneralizedAffineTerm<?> agat,
			final RelationSymbol relationSymbol) {
		if (relationSymbol.isConvexInequality() && SmtSortUtils.isBitvecSort(agat.getSort())) {
			throw new AssertionError("Unsupported inequality/sort combination");
		}
		mPolynomialTerm = Objects.requireNonNull(agat);
		mRelationSymbol = relationSymbol;
		mTrivialityStatus = computeTrivialityStatus(mPolynomialTerm, mRelationSymbol);
	}

	public static PolynomialRelation of(final AbstractGeneralizedAffineTerm<?> agat,
			final RelationSymbol relationSymbol) {
		return new PolynomialRelation(agat, relationSymbol);
	}

	public static PolynomialRelation of(final Script script, final Term term) {
		return of(script, term, TransformInequality.NO_TRANFORMATION);
	}

	public static PolynomialRelation of(final Script script, final Term term,
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
		return PolynomialRelation.of(transformInequality, relationSymbol, polyLhs, polyRhs);
	}

	public static PolynomialRelation of(final Script script, final RelationSymbol relationSymbol, final Term lhs,
			final Term rhs) {
		final IPolynomialTerm lhsPoly = PolynomialTermTransformer.convert(script, lhs);
		final IPolynomialTerm rhsPoly = PolynomialTermTransformer.convert(script, rhs);
		if (lhsPoly == null || rhsPoly == null) {
			throw new AssertionError("lhs or rhs not suitable for polynomial");
		}
		return PolynomialRelation.of(TransformInequality.NO_TRANFORMATION, relationSymbol,
				(AbstractGeneralizedAffineTerm<?>) lhsPoly, (AbstractGeneralizedAffineTerm<?>) rhsPoly);
	}

	public static PolynomialRelation of(final TransformInequality transformInequality, final RelationSymbol relationSymbol,
			final AbstractGeneralizedAffineTerm<?> polyLhs, final AbstractGeneralizedAffineTerm<?> polyRhs) {
		if (polyLhs.getSort() != polyRhs.getSort()) {
			throw new AssertionError("Inconsistent sorts");
		}
		if (!SmtSortUtils.isNumericSort(polyLhs.getSort()) && !SmtSortUtils.isBitvecSort(polyLhs.getSort())) {
			throw new AssertionError("Unsupported sorts");
		}
		if (relationSymbol.isConvexInequality() && SmtSortUtils.isBitvecSort(polyLhs.getSort())) {
			throw new AssertionError("Unsupported inequality/sort combination");
		}
		final AbstractGeneralizedAffineTerm<?> difference = PolynomialTerm.sum(polyLhs,
				PolynomialTerm.mul(polyRhs, Rational.MONE));
		final AbstractGeneralizedAffineTerm<?> polyTerm;
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
					polyTerm = PolynomialTerm.sum(difference, constructConstant(difference.getSort(), Rational.ONE));
					break;
				case GREATER:
					// decrement polynomial term by one
					relationSymbolAfterTransformation = RelationSymbol.GEQ;
					polyTerm = PolynomialTerm.sum(difference, constructConstant(difference.getSort(), Rational.MONE));
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
					polyTerm = PolynomialTerm.sum(difference, constructConstant(difference.getSort(), Rational.ONE));
					break;
				case LEQ:
					// decrement polynomial term by one
					relationSymbolAfterTransformation = RelationSymbol.LESS;
					polyTerm = PolynomialTerm.sum(difference, constructConstant(difference.getSort(), Rational.MONE));
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
		return new PolynomialRelation(polyTerm, relationSymbolAfterTransformation);
	}

	private static AffineTerm constructConstant(final Sort s, final Rational r) {
		return AffineTerm.constructConstant(s, r);
	}

	private static TrivialityStatus computeTrivialityStatus(final AbstractGeneralizedAffineTerm<?> term,
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

	private static TrivialityStatus checkMinMaxValues(final AbstractGeneralizedAffineTerm<?> term,
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

	private static TrivialityStatus computeTrivialityStatus(final AbstractGeneralizedAffineTerm<?> term,
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

	public AbstractGeneralizedAffineTerm<?> getPolynomialTerm() {
		return mPolynomialTerm;
	}

	/**
	 * Returns a term representation of this PolynomialRelation where each summand occurs only positive and the
	 * greater-than relation symbols are replaced by less-than relation symbols. If the term is equivalent to
	 * <i>true</i> (resp. <i>false</i>) we return <i>true</i> (resp. <i>false</i>).
	 */
	public Term toTerm(final Script script) {
		if (mTrivialityStatus == TrivialityStatus.EQUIVALENT_TO_TRUE) {
			return script.term("true");
		} else if (mTrivialityStatus == TrivialityStatus.EQUIVALENT_TO_FALSE) {
			return script.term("false");
		} else {
			assert mTrivialityStatus == TrivialityStatus.NONTRIVIAL;
			final List<Term> lhsSummands = new ArrayList<>();
			final List<Term> rhsSummands = new ArrayList<>();
			for (final Entry<Term, Rational> entry : mPolynomialTerm.getAbstractVariableAsTerm2Coefficient(script)
					.entrySet()) {
				final Term abstractVariableAsTerm = entry.getKey();
				if (SmtSortUtils.isBitvecSort(mPolynomialTerm.getSort())) {
					if (isNegativeAsSignedInt(entry.getValue(), mPolynomialTerm.getSort())) {
						final Rational newCoefficient = PolynomialTermUtils.bringBitvectorValueInRange(
								entry.getValue().mul(Rational.MONE), mPolynomialTerm.getSort());
						rhsSummands.add(SmtUtils.mul(script, newCoefficient, abstractVariableAsTerm));
					} else {
						lhsSummands.add(SmtUtils.mul(script, entry.getValue(), abstractVariableAsTerm));
					}
				} else {
					if (entry.getValue().isNegative()) {
						rhsSummands.add(SmtUtils.mul(script, entry.getValue().abs(), abstractVariableAsTerm));
					} else {
						lhsSummands.add(SmtUtils.mul(script, entry.getValue(), abstractVariableAsTerm));
					}
				}
			}
			if (mPolynomialTerm.getConstant() != Rational.ZERO) {
				if (SmtSortUtils.isBitvecSort(mPolynomialTerm.getSort())) {
					if (isNegativeAsSignedInt(mPolynomialTerm.getConstant(), mPolynomialTerm.getSort())) {
						final Rational newConstant = PolynomialTermUtils.bringBitvectorValueInRange(
								mPolynomialTerm.getConstant().mul(Rational.MONE), mPolynomialTerm.getSort());
						rhsSummands.add(SmtUtils.rational2Term(script, newConstant, mPolynomialTerm.getSort()));
					} else {
						lhsSummands.add(SmtUtils.rational2Term(script, mPolynomialTerm.getConstant(),
								mPolynomialTerm.getSort()));
					}
				} else {
					if (mPolynomialTerm.getConstant().isNegative()) {
						rhsSummands.add(SmtUtils.rational2Term(script, mPolynomialTerm.getConstant().abs(),
								mPolynomialTerm.getSort()));
					} else {
						lhsSummands.add(SmtUtils.rational2Term(script, mPolynomialTerm.getConstant(),
								mPolynomialTerm.getSort()));
					}
				}
			}
			final Term lhsTerm =
					SmtUtils.sum(script, mPolynomialTerm.getSort(), lhsSummands.toArray(new Term[lhsSummands.size()]));
			final Term rhsTerm =
					SmtUtils.sum(script, mPolynomialTerm.getSort(), rhsSummands.toArray(new Term[rhsSummands.size()]));
			final Term result = BinaryRelation.constructLessNormalForm(script, mRelationSymbol, lhsTerm, rhsTerm);
			return result;
		}
	}

	/**
	 * Interpret the value as an integer given by the two's complement
	 * representation of the bitvector value. Return true iff this integer is
	 * negative.
	 */
	private static boolean isNegativeAsSignedInt(final Rational value, final Sort sort) {
		if (!value.isIntegral()) {
			throw new AssertionError();
		}
		if (!SmtSortUtils.isBitvecSort(sort)) {
			throw new AssertionError();
		}
		final BitvectorConstant bc = BitvectorUtils.constructBitvectorConstant(value.numerator(), sort);
		return (bc.toSignedInt().compareTo(BigInteger.ZERO) < 0);
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
				final Term relationToTerm = result.toTerm(script);
				assert script instanceof INonSolverScript || SmtUtils.checkEquivalence(toTerm(script),
						relationToTerm, script) != LBool.SAT : "solveForSubject unsound";
				return result;
			}
		}
	}

	/**
	 * Returns a {@link MultiCaseSolvedBinaryRelation} that is equivalent to this PolynomialRelation or null if we
	 * cannot find such a {@link MultiCaseSolvedBinaryRelation}.
	 */
	public MultiCaseSolvedBinaryRelation solveForSubject(final ManagedScript mgdScript, final Term subject,
			final MultiCaseSolvedBinaryRelation.Xnf xnf, final Set<TermVariable> bannedForDivCapture) {
		return SolveForSubjectUtils.solveForSubject(mgdScript, subject, xnf, this, bannedForDivCapture);
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

	public PolynomialRelation negate(final Script script) {
		return new PolynomialRelation(mPolynomialTerm, mRelationSymbol.negate());
	}

	public PolynomialRelation mul(final Script script, final Rational r) {
		final RelationSymbol resultRelationSymbol = ExplicitLhsPolynomialRelation.swapOfRelationSymbolRequired(r,
				mPolynomialTerm.getSort()) ? mRelationSymbol.swapParameters() : mRelationSymbol;
		return new PolynomialRelation((AbstractGeneralizedAffineTerm<?>) PolynomialTermOperations.mul(mPolynomialTerm, r),
				resultRelationSymbol);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mPolynomialTerm == null) ? 0 : mPolynomialTerm.hashCode());
		result = prime * result + ((mRelationSymbol == null) ? 0 : mRelationSymbol.ordinal());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		final PolynomialRelation other = (PolynomialRelation) obj;
		if (mPolynomialTerm == null) {
			if (other.mPolynomialTerm != null)
				return false;
		} else if (!mPolynomialTerm.equals(other.mPolynomialTerm))
			return false;
		if (mRelationSymbol != other.mRelationSymbol)
			return false;
		return true;
	}

	@Override
	public String toString() {
		final String zero;
		if (SmtSortUtils.isBitvecSort(getPolynomialTerm().getSort())) {
			zero = BitvectorUtils.constructBitvectorConstant(BigInteger.ZERO, getPolynomialTerm().getSort()).toString();
		} else {
			zero = Rational.ZERO.toTerm(mPolynomialTerm.getSort()).toString();
		}
		return String.format("(%s, %s, %s)", mRelationSymbol.toString(), mPolynomialTerm.toString(), zero);
	}

	private static AbstractGeneralizedAffineTerm<?> transformToPolynomialTerm(final Script script, final Term term) {
		return (AbstractGeneralizedAffineTerm<?>) PolynomialTermTransformer.convert(script, term);
	}

	/**
	 * If this {@link PolynomialRelation} has the form `x=l`, where x is a variable
	 * of the underlying (affine) polynomial relation and l is literal, the return
	 * this equality as a {@link SolvedBinaryRelation} where `x` is the left-hand
	 * side and `y` is the right-hand side.
	 */
	public SolvedBinaryRelation isSimpleEquality(final Script script) {
		if (mRelationSymbol != RelationSymbol.EQ) {
			return null;
		}
		if (!isAffine()) {
			return null;
		}
		final Map<Term, Rational> map = ((AffineTerm) mPolynomialTerm).getAbstractVariable2Coefficient();
		final Iterator<Entry<Term, Rational>> it = map.entrySet().iterator();
		if (!it.hasNext()) {
			return null;
		}
		final Entry<Term, Rational> fst = it.next();
		if (it.hasNext()) {
			return null;
		}
		return this.solveForSubject(script, fst.getKey());

	}
}