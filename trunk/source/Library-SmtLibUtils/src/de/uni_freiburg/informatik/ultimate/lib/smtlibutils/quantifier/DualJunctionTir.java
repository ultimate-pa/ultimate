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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryNumericRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol.BvSignedness;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AbstractGeneralizedAffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.ExplicitLhsPolynomialRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.IPolynomialTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.Monomial;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTermOperations;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Transitive inequality resolution (TIR).
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Max Barth
 */
public class DualJunctionTir extends DualJunctionQuantifierElimination {

	private static final boolean HANDLE_DER_OPERATOR = false;
	private static final boolean COMPARE_TO_OLD_RESULT = false;
	private static final boolean ERROR_FOR_OMEGA_TEST_APPLICABILITY = false;

	/**
	 * @see constructor
	 */
	private final boolean mExpensiveEliminations;

	/**
	 * @param expensiveEliminations
	 *            If set to true we do expensive eliminations where auxiliary
	 *            variables and case distinctions are allowed. If set to false
	 *            we do only inexpensive eliminations where non of the above is
	 *            allowed. Note that in the first case we will not do all simple
	 *            eliminations. If you want the full elimination power you
	 *            should two instances of this class.
	 */
	public DualJunctionTir(final ManagedScript script, final IUltimateServiceProvider services,
			final boolean expensiveEliminations) {
		super(script, services);
		mExpensiveEliminations = expensiveEliminations;
	}

	@Override
	public String getName() {
		return "transitive inequality resolution";
	}

	@Override
	public String getAcronym() {
		return "TIR";
	}

	@Override
	public EliminationResult tryToEliminate(final EliminationTask inputEt) {
		final EliminationResult er = tryExhaustivelyToEliminate(inputEt);
		return er;
	}

	/**
	 * Try to iteratively eliminate as many eliminatees as possible using the
	 * given "derHelper". Return null if did not make progress for any
	 * eliminatee.
	 */
	public EliminationResult tryExhaustivelyToEliminate(final EliminationTask inputEt) {
		EliminationTask currentEt = inputEt;
		final LinkedHashSet<TermVariable> aquiredEliminatees = new LinkedHashSet<>();
		while (true) {
			final EliminationResult er = tryToEliminateOne(currentEt);
			if (er == null) {
				// no success, no further iterations
				break;
			}
			aquiredEliminatees.addAll(er.getNewEliminatees());
			currentEt = er.getEliminationTask();
			if (!aquiredEliminatees.isEmpty()) {
				break;
			}
			if (QuantifierUtils.isCorrespondingFiniteJunction(currentEt.getQuantifier(),
					er.getEliminationTask().getTerm())) {
				// we can push the quantifier, no further iterations
				break;
			}
		}
		if (currentEt == inputEt) {
			// only one non-successful iteration
			return null;
		} else {
			return new EliminationResult(currentEt, aquiredEliminatees);
		}
	}

	/**
	 * Try to eliminate some eliminatee using the given "derHelper". Return
	 * immediately after the first successful step (note that a step can be
	 * successful if a case distinction was made and the variable was only
	 * eliminated in for some cases). Return null if did not make progress for
	 * any eliminatee.
	 */
	private EliminationResult tryToEliminateOne(final EliminationTask inputEt) {
		for (final TermVariable eliminatee : inputEt.getEliminatees()) {
			final Set<TermVariable> bannedForDivCapture = new HashSet<>(inputEt.getEliminatees());
			bannedForDivCapture.addAll(inputEt.getContext().getBoundByAncestors());
			final Term resultTerm = tryToEliminateConjuncts(mServices, mScript, inputEt.getQuantifier(),
					inputEt.getTerm(), eliminatee, bannedForDivCapture);
			if (resultTerm != null) {
				if (COMPARE_TO_OLD_RESULT) {
					final Term old = XnfTir.tryToEliminateConjuncts(mServices, mScript, inputEt.getQuantifier(),
							inputEt.getTerm(), eliminatee, bannedForDivCapture);
					if (old != null) {
						final LBool test = SmtUtils.checkEquivalence(old, resultTerm, mScript);
						if (test != LBool.UNSAT) {
							mLogger.info(
									"unexp:" + inputEt.toTerm(mScript) + "   old:" + old + "     new:" + resultTerm);
						}
						assert test == LBool.UNSAT : "unexp:" + inputEt.toTerm(mScript) + "   old:" + old + "     new:"
								+ resultTerm;
					}
				}
				// final ExtendedSimplificationResult esr =
				// SmtUtils.simplifyWithStatistics(mMgdScript, resultTerm,
				// null, mServices, SimplificationTechnique.SIMPLIFY_DDA);
				// final String sizeMessage = String.format("treesize reduction
				// %d, result has
				// %2.1f percent of original
				// size", esr.getReductionOfTreeSize(),
				// esr.getReductionRatioInPercent());
				// mLogger.info(sizeMessage);
				return new EliminationResult(inputEt.update(resultTerm), Collections.emptySet());
			}
		}
		return null;
	}

	public static Term tryToEliminateConjuncts(final IUltimateServiceProvider services, final Script script,
			final int quantifier, final Term disjunct, final TermVariable eliminatee,
			final Set<TermVariable> bannedForDivCapture) {
		final Term[] inputAtoms = QuantifierUtils.getDualFiniteJunction(quantifier, disjunct);
		final List<Term> withEliminatee = Arrays.stream(inputAtoms)
				.filter(x -> Arrays.asList(x.getFreeVars()).contains(eliminatee)).collect(Collectors.toList());
		final List<Term> withoutEliminatee = Arrays.stream(inputAtoms)
				.filter(x -> !Arrays.asList(x.getFreeVars()).contains(eliminatee)).collect(Collectors.toList());
		final ExplicitLhsPolynomialRelations elprs = convert(withEliminatee, script, eliminatee, quantifier);
		if (elprs == null) {
			return null;
		}
		final ExplicitLhsPolynomialRelations bestElprs =
				bestDivision(script, eliminatee, bannedForDivCapture, quantifier, elprs);
		final Term constraint = bestElprs.buildBoundConstraint(services, script, quantifier);
		if (constraint == null) {
			return null;
		}
		withoutEliminatee.add(constraint);
		return QuantifierUtils.applyDualFiniteConnective(script, quantifier, withoutEliminatee);
	}

	private static ExplicitLhsPolynomialRelations bestDivision(final Script script, final TermVariable eliminatee,
			final Set<TermVariable> bannedForDivCapture, final int quantifier,
			final ExplicitLhsPolynomialRelations elprs) {
		final ExplicitLhsPolynomialRelations result = new ExplicitLhsPolynomialRelations(elprs.getSort());
		for (final ExplicitLhsPolynomialRelation elpr : elprs.getLowerBounds()) {
			final ExplicitLhsPolynomialRelation solved = bestDivision(script, bannedForDivCapture, elpr);
			if (solved == null) {
				return null;
			} else {
				result.addSimpleRelation(solved);
			}
		}
		for (final ExplicitLhsPolynomialRelation elpr : elprs.getUpperBounds()) {
			final ExplicitLhsPolynomialRelation solved = bestDivision(script, bannedForDivCapture, elpr);
			if (solved == null) {
				return null;
			} else {
				result.addSimpleRelation(solved);
			}
		}
		for (final Pair<ExplicitLhsPolynomialRelation, ExplicitLhsPolynomialRelation> pair : elprs
				.getAntiDerRelations()) {
			final ExplicitLhsPolynomialRelation solvedLower =
					bestDivision(script, bannedForDivCapture, pair.getFirst());
			final ExplicitLhsPolynomialRelation solvedUpper =
					bestDivision(script, bannedForDivCapture, pair.getSecond());
			if (solvedLower == null) {
				assert solvedUpper == null;
				return null;
			} else {
				final Sort sort = pair.getFirst().getLhsMonomial().getSort();
				if (ExplicitLhsPolynomialRelation.swapOfRelationSymbolRequired(pair.getFirst().getLhsCoefficient(),
						sort)) {
					assert ExplicitLhsPolynomialRelation
							.swapOfRelationSymbolRequired(pair.getSecond().getLhsCoefficient(), sort);
					// upper and lower have been swapped
					result.addAntiDerRelation(solvedUpper, solvedLower);
				} else {
					result.addAntiDerRelation(solvedLower, solvedUpper);
				}
			}

		}
		return result;
	}

	private static ExplicitLhsPolynomialRelation bestDivision(final Script script,
			final Set<TermVariable> bannedForDivCapture, final ExplicitLhsPolynomialRelation elpr) {
		final ExplicitLhsPolynomialRelation solved = elpr.divInvertible(elpr.getLhsCoefficient());
		if (solved != null) {
			return solved;
		}
		final Pair<ExplicitLhsPolynomialRelation, Term> pair =
				elpr.divideByIntegerCoefficient(script, bannedForDivCapture);
		if (pair != null) {
			if (pair.getSecond() != null) {
				throw new AssertionError("not this case");
			}
			return pair.getFirst();
		}
		if (elpr.getLhsCoefficient().isNegative()) {
			return elpr.divInvertible(Rational.MONE);
		} else {
			return elpr;
		}
	}

	private static ExplicitLhsPolynomialRelations convert(final List<Term> withEliminatee, final Script script,
			final TermVariable eliminatee, final int quantifier) {
		final ExplicitLhsPolynomialRelations result = new ExplicitLhsPolynomialRelations(eliminatee.getSort());
		for (final Term t : withEliminatee) {
			final PolynomialRelation polyRel = PolynomialRelation.convert(script, t);
			final ExplicitLhsPolynomialRelation elpr;
			if (polyRel == null) {
				final BinaryNumericRelation bnr = BinaryNumericRelation.convert(t);
				if (bnr == null) {
					return null;
				}
				final SolvedBinaryRelation sbr = bnr.solveForSubject(script, eliminatee);
				if (sbr == null) {
					return null;
				}
				// convert sbr to elpr
				final IPolynomialTerm polyRhs =
						(IPolynomialTerm) new PolynomialTermTransformer(script).transform(sbr.getRightHandSide());
				elpr = new ExplicitLhsPolynomialRelation(sbr.getRelationSymbol(), Rational.ONE,
						new Monomial(sbr.getLeftHandSide(), Rational.ONE), polyRhs);
			} else {
				elpr = ExplicitLhsPolynomialRelation.moveMonomialToLhs(script, eliminatee, polyRel);
				if (elpr == null) {
					return null;
				}
				if (!elpr.getLhsMonomial().isLinear()) {
					return null;
				}
			}
			switch (elpr.getRelationSymbol()) {
			case GEQ:
			case GREATER:
			case LEQ:
			case LESS:
			case BVSGE:
			case BVSGT:
			case BVSLE:
			case BVSLT:
			case BVUGE:
			case BVUGT:
			case BVULE:
			case BVULT:
				result.addSimpleRelation(elpr);
				break;
			case EQ:
				if (quantifier == QuantifiedFormula.EXISTS) {
					if (HANDLE_DER_OPERATOR) {
						throw new AssertionError("Should have really been eliminated by DER");
					} else {
						return null;
					}
				} else if (quantifier == QuantifiedFormula.FORALL) {
					final ExplicitLhsPolynomialRelation lower = elpr.changeRelationSymbol(RelationSymbol.GEQ);
					final ExplicitLhsPolynomialRelation upper = elpr.changeRelationSymbol(RelationSymbol.LEQ);
					result.addAntiDerRelation(lower, upper);
				} else {
					throw new AssertionError("unknown quantifier");
				}
				break;
			case DISTINCT:
				if (quantifier == QuantifiedFormula.EXISTS) {
					final ExplicitLhsPolynomialRelation lower = elpr.changeRelationSymbol(RelationSymbol.GREATER);
					final ExplicitLhsPolynomialRelation upper = elpr.changeRelationSymbol(RelationSymbol.LESS);
					result.addAntiDerRelation(lower, upper);
				} else if (quantifier == QuantifiedFormula.FORALL) {
					if (HANDLE_DER_OPERATOR) {
						throw new AssertionError("Should have really been eliminated by DER");
					} else {
						return null;
					}
				} else {
					throw new AssertionError("unknown quantifier");
				}
				break;
			default:
				throw new AssertionError("unknown relation " + elpr.getRelationSymbol());

			}
		}
		return result;
	}

	private static class ExplicitLhsPolynomialRelations {
		private final Sort mSort;
		private final List<ExplicitLhsPolynomialRelation> mLowerBounds = new ArrayList<>();
		private final List<ExplicitLhsPolynomialRelation> mUpperBounds = new ArrayList<>();
		private final List<Pair<ExplicitLhsPolynomialRelation, ExplicitLhsPolynomialRelation>> mAntiDerBounds =
				new ArrayList<>();

		public ExplicitLhsPolynomialRelations(final Sort sort) {
			mSort = sort;
		}

		void addSimpleRelation(final ExplicitLhsPolynomialRelation bound) {
			switch (bound.getRelationSymbol()) {
			case DISTINCT:
			case EQ:
				throw new AssertionError("should have been split before");
			case GEQ:
			case GREATER:
			case BVUGE:
			case BVUGT:
			case BVSGE:
			case BVSGT:
				mLowerBounds.add(bound);
				break;
			case LEQ:
			case LESS:
			case BVULE:
			case BVULT:
			case BVSLE:
			case BVSLT:
				mUpperBounds.add(bound);
				break;
			default:
				throw new AssertionError("unknown relation symbol " + bound.getRelationSymbol());
			}
		}

		void addAntiDerRelation(final ExplicitLhsPolynomialRelation lowerBound,
				final ExplicitLhsPolynomialRelation upperBound) {
			mAntiDerBounds.add(
					new Pair<ExplicitLhsPolynomialRelation, ExplicitLhsPolynomialRelation>(lowerBound, upperBound));
		}

		public Sort getSort() {
			return mSort;
		}

		public List<ExplicitLhsPolynomialRelation> getLowerBounds() {
			return mLowerBounds;
		}

		public List<ExplicitLhsPolynomialRelation> getUpperBounds() {
			return mUpperBounds;
		}

		public List<Pair<ExplicitLhsPolynomialRelation, ExplicitLhsPolynomialRelation>> getAntiDerRelations() {
			return mAntiDerBounds;
		}

		private Term buildBoundConstraint(final IUltimateServiceProvider services, final Script script,
				final int quantifier) {
			final boolean bvSingleDirectionBounds = SmtSortUtils.isBitvecSort(mSort) && mAntiDerBounds.isEmpty()
					&& (mLowerBounds.isEmpty() != mUpperBounds.isEmpty());
			if (bvSingleDirectionBounds) {
				return checkforSingleDirectionBounds(script, mLowerBounds, mUpperBounds, quantifier);
			}
			final BvSignedness bvSignedness;
			if (SmtSortUtils.isBitvecSort(mSort)) {
				final EnumSet<BvSignedness> bvSignednesses = collectBvSignednesses();
				if (bvSignednesses.equals(EnumSet.allOf(BvSignedness.class))) {
					// we cannot combine strict and unstrict bitvector inequalities
					return null;
				} else if (bvSignednesses.equals(EnumSet.of(BvSignedness.UNSIGNED))) {
					bvSignedness = BvSignedness.UNSIGNED;
				} else if (bvSignednesses.equals(EnumSet.of(BvSignedness.SIGNED))) {
					bvSignedness = BvSignedness.SIGNED;
				} else {
					assert (bvSignednesses.equals(EnumSet.noneOf(BvSignedness.class)));
					assert (mLowerBounds.isEmpty() && mUpperBounds.isEmpty());
					assert !mAntiDerBounds.isEmpty() : "there are no bounds";
					// we are free to choose and take UNSIGNED for no specific reason
					bvSignedness = BvSignedness.UNSIGNED;
				}
			} else {
				bvSignedness = null;
			}

			// final Term withoutAntiDer = buildDualFiniteJunction(script,
			// quantifier, mLowerBounds, mUpperBounds, null);
			final Term antiDer = buildCorrespondingFiniteJunctionForAntiDer(services, quantifier, script, bvSignedness);
			if (antiDer == null) {
				return null;
			}
			return QuantifierUtils.applyDualFiniteConnective(script, quantifier, antiDer);
		}

		private static enum Direction {
			UPPER, LOWER
		}

		private static Term constructConstraintForSingleDirectionBounds(final Term term, final Script script,
				final Sort sort, final boolean signed, final Direction direction, final int quantifier) {
			final BigInteger boundAsBigInt = getMaximalBound(sort, signed, direction);
			final Term boundAsTerm = SmtUtils.constructIntegerValue(script, sort, boundAsBigInt);
			return QuantifierUtils.applyAntiDerOperator(script, quantifier, boundAsTerm, term);
		}

		/**
		 * Construct the maximal possible bounds for bitvector inequalities.
		 * Let n be the length of the bitvector.
		 * <ul>
		 * <li>for unsigned inequalities the maximal lower bound is 0
		 * <li>for unsigned inequalities the maximal upper bound is (2^n)-1
		 * <li>for signed inequalities the maximal lower bound is -2^(n-1)
		 * <li>for signed inequalities the maximal upper bound is (2^(n-1))-1
		 * </ul>
		 */
		private static BigInteger getMaximalBound(final Sort sort, final boolean signed, final Direction direction) {
			final int size = SmtSortUtils.getBitvectorLength(sort);
			final BigInteger pow = BigInteger.TWO.pow(size);
			final BigInteger boundAsBigInt;
			if (signed) {
				switch (direction) {
				case LOWER: {
					boundAsBigInt = pow.divide(BigInteger.TWO).multiply(BigInteger.ONE).negate();
					break;
				}
				case UPPER: {
					boundAsBigInt = pow.divide(BigInteger.TWO).subtract(BigInteger.ONE);
					break;
				}
				default:
					throw new AssertionError("unknown value " + direction);
				}
			} else {
				switch (direction) {
				case LOWER: {
					boundAsBigInt = BigInteger.ZERO;
					break;
				}
				case UPPER: {
					boundAsBigInt = pow.subtract(BigInteger.ONE);
					break;
				}
				default:
					throw new AssertionError("unknown value " + direction);
				}
			}
			return boundAsBigInt;
		}


		/**
		 * Collect the kinds of signedness (signed, unsigned) that occur in all upper
		 * and all lower bounds.
		 */
		private EnumSet<BvSignedness> collectBvSignednesses() {
			final EnumSet<BvSignedness> bvSignednesses = EnumSet.noneOf(BvSignedness.class);
			bvSignednesses.addAll(collectBvSignednesses(mLowerBounds));
			bvSignednesses.addAll(collectBvSignednesses(mUpperBounds));
			return bvSignednesses;
		}

		/**
		 * Collect the kinds of signedness (signed, unsigned) that occur in the given
		 * bounds.
		 */
		private static EnumSet<BvSignedness> collectBvSignednesses(final List<ExplicitLhsPolynomialRelation> bounds) {
			final EnumSet<BvSignedness> bvSignednesses = EnumSet.noneOf(BvSignedness.class);
			for (final ExplicitLhsPolynomialRelation bound : bounds) {
				if (bound.getRelationSymbol().isUnSignedBvRelation()) {
					bvSignednesses.add(BvSignedness.UNSIGNED);
				} else if (bound.getRelationSymbol().isSignedBvRelation()) {
					bvSignednesses.add(BvSignedness.SIGNED);
				}
			}
			return bvSignednesses;
		}

		/**
		 * Calculates the equivalent Quantifier free Term, if BitVector Sort,
		 * one Bounds List is empty and the RelationSymbol is Strict.
		 */
		private Term checkforSingleDirectionBounds(final Script script,
				final List<ExplicitLhsPolynomialRelation> lowerBounds,
				final List<ExplicitLhsPolynomialRelation> upperBounds, final int quantifier) {
			final Direction direction;
			List<ExplicitLhsPolynomialRelation> bounds;
			if (upperBounds.isEmpty()) {
				if (quantifier == QuantifiedFormula.EXISTS) {
					direction = Direction.UPPER;
				} else if (quantifier == QuantifiedFormula.FORALL) {
					direction = Direction.LOWER;
				} else {
					throw new AssertionError("Unknown quantifier " + quantifier);
				}
				bounds = lowerBounds;
			} else if (lowerBounds.isEmpty()) {
				if (quantifier == QuantifiedFormula.EXISTS) {
					direction = Direction.LOWER;
				} else if (quantifier == QuantifiedFormula.FORALL) {
					direction = Direction.UPPER;
				} else {
					throw new AssertionError("Unknown quantifier " + quantifier);
				}
				bounds = upperBounds;
			} else {
				return null;
			}
			return constructConstraintForSingleDirectionBounds(script, quantifier, direction, bounds);
		}

		private Term constructConstraintForSingleDirectionBounds(final Script script, final int quantifier,
				final Direction direction, final List<ExplicitLhsPolynomialRelation> bounds) {
			final List<Term> dualFiniteJunction = new ArrayList<>();
			for (final ExplicitLhsPolynomialRelation bound : bounds) {
				if ((quantifier == QuantifiedFormula.EXISTS) && (bound.getRelationSymbol().isStrictRelation())) {
					dualFiniteJunction.add(constructConstraintForSingleDirectionBounds(bound.getRhs().toTerm(script),
							script, bound.getRhs().getSort(), bound.getRelationSymbol().isSignedBvRelation(), direction,
							quantifier));
				} else if ((quantifier == QuantifiedFormula.FORALL)
						&& (!bound.getRelationSymbol().isStrictRelation())) {
					dualFiniteJunction.add(constructConstraintForSingleDirectionBounds(bound.getRhs().toTerm(script),
							script, bound.getRhs().getSort(), bound.getRelationSymbol().isSignedBvRelation(), direction,
							quantifier));
				} else {
					// does not contribute to constraint
				}
			}
			return QuantifierUtils.applyDualFiniteConnective(script, quantifier, dualFiniteJunction);
		}

		private Term buildCorrespondingFiniteJunctionForAntiDer(final IUltimateServiceProvider services,
				final int quantifier, final Script script, final BvSignedness bvSignedness) {

			final int numberOfCorrespondingFiniteJuncts = (int) Math.pow(2, mAntiDerBounds.size());
			final Term[] correspondingFiniteJuncts = new Term[numberOfCorrespondingFiniteJuncts];

			for (int i = 0; i < numberOfCorrespondingFiniteJuncts; i++) {
				if (!services.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(this.getClass(),
							"build " + i + " of " + numberOfCorrespondingFiniteJuncts + " xjuncts");
				}
				final List<ExplicitLhsPolynomialRelation> lowerBounds = new ArrayList<>(mLowerBounds);
				final List<ExplicitLhsPolynomialRelation> upperBounds = new ArrayList<>(mUpperBounds);
				for (int k = 0; k < mAntiDerBounds.size(); k++) {
					// zero means lower - one means upper
					if (BigInteger.valueOf(i).testBit(k)) {
						upperBounds.add(mAntiDerBounds.get(k).getSecond());
					} else {
						lowerBounds.add(mAntiDerBounds.get(k).getFirst());
					}
				}
				correspondingFiniteJuncts[i] = buildDualFiniteJunction(script, quantifier, lowerBounds, upperBounds,
						bvSignedness);
				if (correspondingFiniteJuncts[i] == null) {
					return null;
				}
			}
			return QuantifierUtils.applyCorrespondingFiniteConnective(script, quantifier, correspondingFiniteJuncts);
		}


		private Term buildDualFiniteJunction(final Script script, final int quantifier,
				final List<ExplicitLhsPolynomialRelation> lowerBounds,
				final List<ExplicitLhsPolynomialRelation> upperBounds, final BvSignedness bvSignedness) {
			if (lowerBounds.size() == 0 || upperBounds.size() == 0) {
				return QuantifierUtils.applyDualFiniteConnective(script, quantifier);
			}
			final boolean allLowerCoefficientsOne = allCoefficientsOne(lowerBounds);
			final boolean allUpperCoefficientsOne = allCoefficientsOne(upperBounds);
			if (allLowerCoefficientsOne != allUpperCoefficientsOne) {
				if (ERROR_FOR_OMEGA_TEST_APPLICABILITY) {
					final String message = "we need the exact shadows from the omega test";
					throw new AssertionError(message);
				} else {
					// TODO: log message
					return null;
				}
			}
			if (!allLowerCoefficientsOne && !allUpperCoefficientsOne) {
				if (ERROR_FOR_OMEGA_TEST_APPLICABILITY) {
					final String message = "we need the omega test";
					throw new AssertionError(message);
				} else {
					// TODO: log message
					return null;
				}
			}
			final Term[] allCombinations = new Term[lowerBounds.size() * upperBounds.size()];

			int i = 0;
			for (final ExplicitLhsPolynomialRelation lower : lowerBounds) {
				for (final ExplicitLhsPolynomialRelation upper : upperBounds) {

					allCombinations[i] = combine(script, quantifier, lower, upper, bvSignedness);
					if (allCombinations[i] == null) {
						// null e.g., if lower and upper RelationSymbols are strict BV
						// relations and quantifier is exists
						return null;
					}
					i++;

				}
			}
			return QuantifierUtils.applyDualFiniteConnective(script, quantifier, allCombinations);
		}

		private static boolean allCoefficientsOne(final List<ExplicitLhsPolynomialRelation> bounds) {
			for (final ExplicitLhsPolynomialRelation bound : bounds) {
				if (!bound.getLhsMonomial().isLinear()) {
					throw new AssertionError("cannot handle proper monomial");
				}
				if (bound.getLhsCoefficient().isNegative()) {
					throw new AssertionError("cannot handle negative coefficients");
				}
				if (!bound.getLhsCoefficient().equals(Rational.ONE)) {
					return false;
				}
			}
			return true;
		}

		private Term combine(final Script script, final int quantifier, final ExplicitLhsPolynomialRelation lower,
				final ExplicitLhsPolynomialRelation upper, final BvSignedness bvSignedness) {

			final Pair<RelationSymbol, Rational> relSymbAndOffset = computeRelationSymbolAndOffset(quantifier,
					lower.getRelationSymbol(), upper.getRelationSymbol(), lower.getRhs().getSort(), bvSignedness);
			assert relSymbAndOffset.getSecond().equals(Rational.ZERO)
					|| relSymbAndOffset.getSecond().equals(Rational.ONE)
					|| relSymbAndOffset.getSecond().equals(Rational.MONE);
			final IPolynomialTerm lhs = lower.getRhs();
			final IPolynomialTerm rhs = upper.getRhs();

			final Term result;
			if (SmtSortUtils.isBitvecSort(lower.getRhs().getSort())) {
				if (!relSymbAndOffset.getSecond().equals(Rational.ZERO)) {
					// for bitvectors we cannot handle offsets
					// e.g., required if we combine two strict
					// relations for an existential quantifier
					result = null;
				} else {
					result = relSymbAndOffset.getFirst().constructTerm(script, lhs.toTerm(script), rhs.toTerm(script));
				}
			} else {
				final IPolynomialTerm negatedRhs = PolynomialTermOperations.mul(rhs, Rational.MONE);
				IPolynomialTerm resultRhs;
				if (relSymbAndOffset.getSecond().equals(Rational.ZERO)) {
					resultRhs = PolynomialTerm.sum(lhs, negatedRhs);
				} else {
					resultRhs = PolynomialTerm.sum(lhs, negatedRhs,
							new AffineTerm(lhs.getSort(), relSymbAndOffset.getSecond(), Collections.emptyMap()));
				}
				result = new PolynomialRelation(script, (AbstractGeneralizedAffineTerm<?>) resultRhs,
						relSymbAndOffset.getFirst()).positiveNormalForm(script);
			}
			return result;
		}

	}

	private static Pair<RelationSymbol, Rational> computeRelationSymbolAndOffset(final int quantifier,
			final RelationSymbol lowerBoundRelationSymbol, final RelationSymbol upperBoundRelationSymbol,
			final Sort sort, final BvSignedness bvSignedness) {
		final RelationSymbol resultRelationSymbol;
		final Rational offset;
		if (lowerBoundRelationSymbol.isRelationSymbolGE() && upperBoundRelationSymbol.isRelationSymbolLE()) {
			resultRelationSymbol = upperBoundRelationSymbol.getInequality(upperBoundRelationSymbol.isStrictRelation(),
					sort, bvSignedness);
			if ((quantifier == QuantifiedFormula.FORALL)
					&& (SmtSortUtils.isIntSort(sort) || SmtSortUtils.isBitvecSort(sort))) {
				offset = Rational.MONE;
			} else {
				offset = Rational.ZERO;
			}
		} else if ((lowerBoundRelationSymbol.isRelationSymbolGE() && upperBoundRelationSymbol.isRelationSymbolLT())
				|| (lowerBoundRelationSymbol.isRelationSymbolGT() && upperBoundRelationSymbol.isRelationSymbolLE())) {
			if (quantifier == QuantifiedFormula.EXISTS) {
				resultRelationSymbol = upperBoundRelationSymbol.getInequality(true, sort, bvSignedness);
			} else if (quantifier == QuantifiedFormula.FORALL) {
				resultRelationSymbol = upperBoundRelationSymbol.getInequality(false, sort, bvSignedness);
			} else {
				throw new AssertionError("unknown quantifier");
			}
			offset = Rational.ZERO;
		} else if (lowerBoundRelationSymbol.isRelationSymbolGT() && upperBoundRelationSymbol.isRelationSymbolLT()) {
			resultRelationSymbol = upperBoundRelationSymbol.getInequality(upperBoundRelationSymbol.isStrictRelation(),
					sort, bvSignedness);
			if ((quantifier == QuantifiedFormula.EXISTS)
					&& (SmtSortUtils.isIntSort(sort) || SmtSortUtils.isBitvecSort(sort))) {
				offset = Rational.ONE;
			} else {
				offset = Rational.ZERO;
			}
		} else {
			throw new AssertionError(String.format("Unsupported relation symbols: Lower %s, Upper %s",
					lowerBoundRelationSymbol, upperBoundRelationSymbol));
		}
		return new Pair<RelationSymbol, Rational>(resultRelationSymbol, offset);
	}
}
