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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.EliminationTask;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
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
	/**
	 * @see constructor
	 */
	private final boolean mExpensiveEliminations;

	/**
	 * @param expensiveEliminations
	 *            If set to true we do expensive eliminations where auxiliary
	 *            variables and case distinctions are allowed. If set to false we do
	 *            only inexpensive eliminations where non of the above is allowed.
	 *            Note that in the first case we will not do all simple
	 *            eliminations. If you want the full elimination power you should
	 *            two instances of this class.
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
	 * Try to iteratively eliminate as many eliminatees as possible using the given
	 * "derHelper". Return null if did not make progress for any eliminatee.
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
	 * eliminated in for some cases). Return null if did not make progress
	 * for any eliminatee.
	 */
	private EliminationResult tryToEliminateOne(final EliminationTask inputEt) {
		for (final TermVariable eliminatee : inputEt.getEliminatees()) {
			final Term resultTerm = XnfTir.tryToEliminateConjuncts(mServices, mScript, inputEt.getQuantifier(),
//			final Term resultTerm = tryToEliminateConjuncts(mServices, mScript, inputEt.getQuantifier(),
					inputEt.getTerm(), eliminatee, inputEt.getBannedForDivCapture());
			if (resultTerm != null) {
//				final ExtendedSimplificationResult esr = SmtUtils.simplifyWithStatistics(mMgdScript, resultTerm, null, mServices, SimplificationTechnique.SIMPLIFY_DDA);
//				final String sizeMessage = String.format("treesize reduction %d, result has %2.1f percent of original size",
//						esr.getReductionOfTreeSize(), esr.getReductionRatioInPercent());
//				mLogger.info(sizeMessage);
				return new EliminationResult(
						new EliminationTask(inputEt.getQuantifier(), inputEt.getEliminatees(), resultTerm),
						Collections.emptySet());
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
		final List<ExplicitLhsPolynomialRelation> elprs = convert(withEliminatee, script, eliminatee);
		if (elprs == null) {
			return null;
		}
		TirBounds tirBounds = computeTirBoundForUnifiedLhs(eliminatee, quantifier, elprs);
		if (tirBounds == null) {
			tirBounds = computeTirBoundSolveForSubject(script, eliminatee, bannedForDivCapture, quantifier, elprs);
			if (tirBounds == null && SmtSortUtils.isIntSort(eliminatee.getSort())) {
				tirBounds = computeTirBoundSolveForSubjectInt(script, eliminatee, bannedForDivCapture, quantifier,
						elprs);
				if (tirBounds == null && false) {
					final List<ExplicitLhsPolynomialRelation> unifiedElprs = unifyByMultiplication(script, eliminatee,
							bannedForDivCapture, quantifier, elprs);
					tirBounds = computeTirBoundForUnifiedLhs(eliminatee, quantifier, unifiedElprs);
				}
			}
		}
		if (tirBounds == null) {
			return null;
		}
		final Term constraint = tirBounds.buildBoundConstraint(services, script, quantifier);
		withoutEliminatee.add(constraint);
		return QuantifierUtils.applyDualFiniteConnective(script, quantifier, withoutEliminatee);
	}

	private static TirBounds computeTirBoundForUnifiedLhs(final TermVariable eliminatee, final int quantifier,
			final List<ExplicitLhsPolynomialRelation> elprs) {
		final TirBounds result = new TirBounds();
		Rational firstCoeffcient = null;
		Monomial firstMonomial = null;
		for (final ExplicitLhsPolynomialRelation elpr : elprs) {
			if (firstCoeffcient == null) {
				firstCoeffcient = elpr.getLhsCoefficient();
				assert firstMonomial == null;
				firstMonomial = elpr.getLhsMonomial();
			} else {
				if (!firstCoeffcient.equals(elpr.getLhsCoefficient()) || !firstMonomial.equals(elpr.getLhsMonomial())) {
					return null;
				}
			}
			switch (elpr.getRelationSymbol()) {
			case DISTINCT:
				if (quantifier == QuantifiedFormula.EXISTS) {
					result.addDerBound(new Bound(RelationSymbol.GREATER, elpr.getRhs()),
							new Bound(RelationSymbol.LESS, elpr.getRhs()));
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
			case EQ:
				if (quantifier == QuantifiedFormula.EXISTS) {
					if (HANDLE_DER_OPERATOR) {
						throw new AssertionError("Should have really been eliminated by DER");
					} else {
						return null;
					}
				} else if (quantifier == QuantifiedFormula.FORALL) {
					result.addDerBound(new Bound(RelationSymbol.GEQ, elpr.getRhs()),
							new Bound(RelationSymbol.LEQ, elpr.getRhs()));
				} else {
					throw new AssertionError("unknown quantifier");
				}
				break;
			case GEQ:
			case GREATER:
			case LEQ:
			case LESS:
				result.addSimpleBound(new Bound(elpr.getRelationSymbol(), elpr.getRhs()));
				break;
			default:
				throw new AssertionError("unknown relation symbol " + elpr.getRelationSymbol());
			}
		}
		return result;
	}

	private static TirBounds computeTirBoundSolveForSubject(final Script script, final TermVariable eliminatee,
			final Set<TermVariable> bannedForDivCapture, final int quantifier,
			final List<ExplicitLhsPolynomialRelation> elprs) {
		final TirBounds result = new TirBounds();
		for (final ExplicitLhsPolynomialRelation elpr : elprs) {
			if (!elpr.getLhsMonomial().isLinear()) {
				return null;
			}
			final ExplicitLhsPolynomialRelation solved = elpr.divInvertible(elpr.getLhsCoefficient());
			if (solved == null) {
				return null;
			}
			switch (solved.getRelationSymbol()) {
			case DISTINCT:
				if (quantifier == QuantifiedFormula.EXISTS) {
					result.addDerBound(new Bound(RelationSymbol.GREATER, solved.getRhs()),
							new Bound(RelationSymbol.LESS, solved.getRhs()));
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
			case EQ:
				if (quantifier == QuantifiedFormula.EXISTS) {
					if (HANDLE_DER_OPERATOR) {
						throw new AssertionError("Should have really been eliminated by DER");
					} else {
						return null;
					}
				} else if (quantifier == QuantifiedFormula.FORALL) {
					result.addDerBound(new Bound(RelationSymbol.GEQ, solved.getRhs()),
							new Bound(RelationSymbol.LEQ, solved.getRhs()));
				} else {
					throw new AssertionError("unknown quantifier");
				}
				break;
			case GEQ:
			case GREATER:
			case LEQ:
			case LESS:
				result.addSimpleBound(new Bound(solved.getRelationSymbol(), solved.getRhs()));
				break;
			default:
				throw new AssertionError("unknown relation symbol " + solved.getRelationSymbol());
			}
		}
		return result;
	}

	private static TirBounds computeTirBoundSolveForSubjectInt(final Script script, final TermVariable eliminatee,
			final Set<TermVariable> bannedForDivCapture, final int quantifier,
			final List<ExplicitLhsPolynomialRelation> elprs) {
		final TirBounds result = new TirBounds();
		for (final ExplicitLhsPolynomialRelation elpr : elprs) {
			if (!elpr.getLhsMonomial().isLinear()) {
				return null;
			}
			ExplicitLhsPolynomialRelation tmp;
			if (elpr.getLhsCoefficient().isNegative()) {
				tmp = elpr.mul(Rational.MONE, script);
			} else {
				tmp = elpr;
			}
			switch (tmp.getRelationSymbol()) {
			case DISTINCT:
				if (quantifier == QuantifiedFormula.EXISTS) {
					final ExplicitLhsPolynomialRelation lower = tmp.changeRelationSymbol(RelationSymbol.GREATER);
					final ExplicitLhsPolynomialRelation upper = tmp.changeRelationSymbol(RelationSymbol.LESS);
					final SolvedBinaryRelation solvedLower = lower.divideByIntegerCoefficientForInequalities(script,
							bannedForDivCapture);
					final SolvedBinaryRelation solvedUpper = upper.divideByIntegerCoefficientForInequalities(script,
							bannedForDivCapture);
					if (solvedLower == null) {
						assert solvedUpper == null;
						return null;
					} else {
						assert solvedUpper != null;
					}
					result.addDerBound(
							new Bound(solvedLower.getRelationSymbol(),
									toPolynomial(script, solvedLower.getRightHandSide())),
							new Bound(solvedUpper.getRelationSymbol(),
									toPolynomial(script, solvedUpper.getRightHandSide())));
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
			case EQ:
				if (quantifier == QuantifiedFormula.EXISTS) {
					if (HANDLE_DER_OPERATOR) {
						throw new AssertionError("Should have really been eliminated by DER");
					} else {
						return null;
					}
				} else if (quantifier == QuantifiedFormula.FORALL) {
					final ExplicitLhsPolynomialRelation lower = tmp.changeRelationSymbol(RelationSymbol.GEQ);
					final ExplicitLhsPolynomialRelation upper = tmp.changeRelationSymbol(RelationSymbol.LEQ);
					final SolvedBinaryRelation solvedLower = lower.divideByIntegerCoefficientForInequalities(script,
							bannedForDivCapture);
					final SolvedBinaryRelation solvedUpper = upper.divideByIntegerCoefficientForInequalities(script,
							bannedForDivCapture);
					if (solvedLower == null) {
						return null;
					}
					result.addDerBound(
							new Bound(solvedLower.getRelationSymbol(),
									toPolynomial(script, solvedLower.getRightHandSide())),
							new Bound(solvedUpper.getRelationSymbol(),
									toPolynomial(script, solvedUpper.getRightHandSide())));
				} else {
					throw new AssertionError("unknown quantifier");
				}
				break;
			case GEQ:
			case GREATER:
			case LEQ:
			case LESS:
				final SolvedBinaryRelation solved = tmp.divideByIntegerCoefficientForInequalities(script,
						bannedForDivCapture);
				if (solved == null) {
					return null;
				}
				result.addSimpleBound(
						new Bound(solved.getRelationSymbol(), toPolynomial(script, solved.getRightHandSide())));
				break;
			default:
				throw new AssertionError("unknown relation symbol " + tmp.getRelationSymbol());
			}
		}
		return result;
	}

	private static IPolynomialTerm toPolynomial(final Script script, final Term term) {
		return (IPolynomialTerm) new PolynomialTermTransformer(script).transform(term);
	}

	private static List<ExplicitLhsPolynomialRelation> unifyByMultiplication(final Script script,
			final TermVariable eliminatee, final Set<TermVariable> bannedForDivCapture, final int quantifier,
			final List<ExplicitLhsPolynomialRelation> elprs) {
		// lcm of absolute values of coefficients
		Rational lcm = Rational.ONE;
		for (final ExplicitLhsPolynomialRelation elpr : elprs) {
			if (!elpr.getLhsMonomial().isLinear()) {
				return null;
			}
			if (!SmtSortUtils.isIntSort(elpr.getLhsMonomial().getSort())) {
				throw new AssertionError("only for int");
			}
			final Rational tmpProd = lcm.mul(elpr.getLhsCoefficient().abs());
			final Rational tmpGcd = lcm.gcd(elpr.getLhsCoefficient().abs());
			lcm = tmpProd.div(tmpGcd);
			assert lcm.isIntegral();
		}
		final List<ExplicitLhsPolynomialRelation> result = new ArrayList<>();
		for (final ExplicitLhsPolynomialRelation elpr : elprs) {
			final Rational factor = lcm.div(elpr.getLhsCoefficient());
			result.add(elpr.mul(factor, script));
		}
		return result;
	}

	private static List<ExplicitLhsPolynomialRelation> convert(final List<Term> withEliminatee, final Script script,
			final TermVariable eliminatee) {

		final List<ExplicitLhsPolynomialRelation> result = new ArrayList<>();
		for (final Term t : withEliminatee) {
			final PolynomialRelation polyRel = PolynomialRelation.convert(script, t);
			if (polyRel == null) {
				return null;
			}
			final ExplicitLhsPolynomialRelation elpr = ExplicitLhsPolynomialRelation.moveMonomialToLhs(script,
					eliminatee, polyRel);
			if (elpr == null) {
				return null;
			}
			result.add(elpr);
		}
		return result;
	}

	private static class Bound {
		private final RelationSymbol mRelationSymbol;
		private final IPolynomialTerm mPolynomialTerm;

		public Bound(final RelationSymbol relationSymbol, final IPolynomialTerm polynomialTerm) {
			super();
			mRelationSymbol = relationSymbol;
			mPolynomialTerm = polynomialTerm;
		}

		public RelationSymbol getRelationSymbol() {
			return mRelationSymbol;
		}

		public IPolynomialTerm getPolynomialTerm() {
			return mPolynomialTerm;
		}

		@Override
		public String toString() {
			return mRelationSymbol + " " + mPolynomialTerm;
		}
	}

	private static class TirBounds {
		private final List<Bound> mLowerBounds = new ArrayList<>();
		private final List<Bound> mUpperBounds = new ArrayList<>();
		private final List<Pair<Bound, Bound>> mAntiDerBounds = new ArrayList<>();

		void addSimpleBound(final Bound bound) {
			switch (bound.getRelationSymbol()) {
			case DISTINCT:
			case EQ:
				throw new AssertionError("should have been split before");
			case GEQ:
			case GREATER:
				mLowerBounds.add(bound);
				break;
			case LEQ:
			case LESS:
				mUpperBounds.add(bound);
				break;
			default:
				throw new AssertionError("unknown relation symbol " + bound.getRelationSymbol());
			}
		}

		void addDerBound(final Bound lowerBound, final Bound upperBound) {
			mAntiDerBounds.add(new Pair<Bound, Bound>(lowerBound, upperBound));
		}

		private Term buildBoundConstraint(final IUltimateServiceProvider services, final Script script,
				final int quantifier) {
			final Term withoutAntiDer = buildDualFiniteJunction(script, quantifier, mLowerBounds, mUpperBounds);
			final Term antiDer = buildCorrespondingFiniteJunctionForAntiDer(services, quantifier, script);
			return QuantifierUtils.applyDualFiniteConnective(script, quantifier, antiDer);
		}

		private Term buildCorrespondingFiniteJunctionForAntiDer(final IUltimateServiceProvider services,
				final int quantifier, final Script script) {
			final int numberOfCorrespondingFiniteJuncts = (int) Math.pow(2, mAntiDerBounds.size());
			final Term[] correspondingFiniteJuncts = new Term[numberOfCorrespondingFiniteJuncts];

			for (int i = 0; i < numberOfCorrespondingFiniteJuncts; i++) {
				if (!services.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(this.getClass(),
							"build " + i + " of " + numberOfCorrespondingFiniteJuncts + " xjuncts");
				}
				final ArrayList<Bound> lowerBounds = new ArrayList<>(mLowerBounds);
				final ArrayList<Bound> upperBounds = new ArrayList<>(mUpperBounds);
				for (int k = 0; k < mAntiDerBounds.size(); k++) {
					// zero means lower - one means upper
					if (BigInteger.valueOf(i).testBit(k)) {
						upperBounds.add(mAntiDerBounds.get(k).getSecond());
					} else {
						lowerBounds.add(mAntiDerBounds.get(k).getFirst());
					}
				}
				correspondingFiniteJuncts[i] = buildDualFiniteJunction(script, quantifier, lowerBounds, upperBounds);
			}
			return QuantifierUtils.applyCorrespondingFiniteConnective(script, quantifier, correspondingFiniteJuncts);
		}

		private Term buildDualFiniteJunction(final Script script, final int quantifier, final List<Bound> lowerBounds,
				final List<Bound> upperBounds) {
			final Term[] allCombinations = new Term[lowerBounds.size() * upperBounds.size()];
			int i = 0;
			for (final Bound lower : lowerBounds) {
				for (final Bound upper : upperBounds) {
					allCombinations[i] = combine(script, quantifier, lower, upper);
					i++;
				}
			}
			return QuantifierUtils.applyDualFiniteConnective(script, quantifier, allCombinations);
		}

		private Term combine(final Script script, final int quantifier, final Bound lower, final Bound upper) {
			final Pair<RelationSymbol, Rational> relSymbAndOffset = computeRelationSymbolAndOffset(quantifier,
					lower.getRelationSymbol(), upper.getRelationSymbol(), lower.getPolynomialTerm().getSort());
			assert relSymbAndOffset.getSecond().equals(Rational.ZERO)
					|| relSymbAndOffset.getSecond().equals(Rational.ONE)
					|| relSymbAndOffset.getSecond().equals(Rational.MONE);
			final IPolynomialTerm lhs = lower.getPolynomialTerm();
			final IPolynomialTerm rhs = upper.getPolynomialTerm();
			final IPolynomialTerm negatedRhs = PolynomialTermOperations.mul(rhs, Rational.MONE);
			IPolynomialTerm resultRhs;
			if (relSymbAndOffset.getSecond().equals(Rational.ZERO)) {
				resultRhs = PolynomialTerm.sum(lhs, negatedRhs);
			} else {
				resultRhs = PolynomialTerm.sum(lhs, negatedRhs,
						new AffineTerm(lhs.getSort(), relSymbAndOffset.getSecond(), Collections.emptyMap()));
			}
			return new PolynomialRelation(script, (AbstractGeneralizedAffineTerm<?>) resultRhs,
					relSymbAndOffset.getFirst()).positiveNormalForm(script);
		}

		private Pair<RelationSymbol, Rational> computeRelationSymbolAndOffset(final int quantifier,
				final RelationSymbol lowerBoundRelationSymbol, final RelationSymbol upperBoundRelationSymbol,
				final Sort sort) {
			final RelationSymbol resultRelationSymbol;
			final Rational offset;
			if (lowerBoundRelationSymbol.equals(RelationSymbol.GEQ)
					&& upperBoundRelationSymbol.equals(RelationSymbol.LEQ)) {
				resultRelationSymbol = RelationSymbol.LEQ;
				if (SmtSortUtils.isRealSort(sort)) {
					offset = Rational.ZERO;
				} else if (SmtSortUtils.isIntSort(sort)) {
					if (quantifier == QuantifiedFormula.EXISTS) {
						offset = Rational.ZERO;
					} else if (quantifier == QuantifiedFormula.FORALL) {
						offset = Rational.MONE;
					} else {
						throw new AssertionError("unknown quantifier");
					}
				} else {
					throw new AssertionError("Unsupported sort " + sort);
				}

			} else if (lowerBoundRelationSymbol.equals(RelationSymbol.GEQ)
					&& upperBoundRelationSymbol.equals(RelationSymbol.LESS)
					|| (lowerBoundRelationSymbol.equals(RelationSymbol.GREATER)
							&& upperBoundRelationSymbol.equals(RelationSymbol.LEQ))) {
				if (quantifier == QuantifiedFormula.EXISTS) {
					resultRelationSymbol = RelationSymbol.LESS;
				} else if (quantifier == QuantifiedFormula.FORALL) {
					resultRelationSymbol = RelationSymbol.LEQ;
				} else {
					throw new AssertionError("unknown quantifier");
				}
				offset = Rational.ZERO;
			} else if (lowerBoundRelationSymbol.equals(RelationSymbol.GREATER)
					&& upperBoundRelationSymbol.equals(RelationSymbol.LESS)) {
				resultRelationSymbol = RelationSymbol.LESS;
				if (SmtSortUtils.isRealSort(sort)) {
					offset = Rational.ZERO;
				} else if (SmtSortUtils.isIntSort(sort)) {
					if (quantifier == QuantifiedFormula.EXISTS) {
						offset = Rational.ONE;
					} else if (quantifier == QuantifiedFormula.FORALL) {
						offset = Rational.ZERO;
					} else {
						throw new AssertionError("unknown quantifier");
					}
				} else {
					throw new AssertionError("Unsupported sort " + sort);
				}
			} else {
				// <pre>
				// TODO #bvineq 20201017 Matthias:
				// * Cases for new relation symbols probably have to be added above.
				// * We probably need a special solution for upper bounds of
				// the form "bvult 0" because is this case we should subtract -1
				// * Idea: omit call to this method and replace result by "false"
				// </pre>
				throw new AssertionError(String.format("Unsupported relation symbols: Lower %s, Upper %s",
						lowerBoundRelationSymbol, upperBoundRelationSymbol));
			}
			return new Pair<RelationSymbol, Rational>(resultRelationSymbol, offset);
		}

	}

}
