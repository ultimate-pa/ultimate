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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
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
	/**
	 * @see constructor
	 */
	private final boolean mExpensiveEliminations;

	/**
	 * @param expensiveEliminations
	 *            If set to true we do expensive eliminations where auxiliary variables and case distinctions are
	 *            allowed. If set to false we do only inexpensive eliminations where non of the above is allowed. Note
	 *            that in the first case we will not do all simple eliminations. If you want the full elimination power
	 *            you should two instances of this class.
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
	 * Try to iteratively eliminate as many eliminatees as possible using the given "derHelper". Return null if did not
	 * make progress for any eliminatee.
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
	 * Try to eliminate some eliminatee using the given "derHelper". Return immediately after the first successful step
	 * (note that a step can be successful if a case distinction was made and the variable was only eliminated in for
	 * some cases). Return null if did not make progress for any eliminatee.
	 */
	private EliminationResult tryToEliminateOne(final EliminationTask inputEt) {
		for (final TermVariable eliminatee : inputEt.getEliminatees()) {
			final Term resultTerm = tryToEliminateConjuncts(mServices, mScript, inputEt.getQuantifier(),
					inputEt.getTerm(), eliminatee, inputEt.getBannedForDivCapture());
			if (resultTerm != null) {
				if (COMPARE_TO_OLD_RESULT) {
					final Term old = XnfTir.tryToEliminateConjuncts(mServices, mScript, inputEt.getQuantifier(),
							inputEt.getTerm(), eliminatee, inputEt.getBannedForDivCapture());
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
		TirBounds tirBounds = null;
		if (true) {
			final ExplicitLhsPolynomialRelations elprs = convert(withEliminatee, script, eliminatee, quantifier);
			if (elprs == null) {
				return null;
			}
			tirBounds = computeTirBoundForUnifiedLhs(eliminatee, quantifier, elprs);
			if (tirBounds == null) {
				final ExplicitLhsPolynomialRelations elprsDivInvertible = unifyByIntertibleDivision(script, eliminatee, bannedForDivCapture, quantifier, elprs);
				if (elprsDivInvertible != null) {
					tirBounds = computeTirBoundForUnifiedLhs(eliminatee, quantifier, elprsDivInvertible);
				} else if (SmtSortUtils.isIntSort(eliminatee.getSort())) {
					final ExplicitLhsPolynomialRelations elprsDivInt;
					if (true) {
						elprsDivInt = unifyByDivisionForInt(script, eliminatee, bannedForDivCapture, quantifier, elprs);
					} else {
						elprsDivInt = unifyByMultiplication(script, eliminatee, bannedForDivCapture, quantifier, elprs);
					}
					if (elprsDivInt != null) {
						tirBounds = computeTirBoundForUnifiedLhs(eliminatee, quantifier, elprsDivInt);
					} else {
						return null;
					}
				} else {
					return null;
				}
			}
		} else {
			final List<ExplicitLhsPolynomialRelation> elprs = convertOld(withEliminatee, script, eliminatee);
			if (elprs == null) {
				return null;
			}
			computeTirBoundForUnifiedLhs(eliminatee, quantifier, elprs);
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
					result.addAntiDerBound(new Bound(RelationSymbol.GREATER, elpr.getRhs()),
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
					result.addAntiDerBound(new Bound(RelationSymbol.GEQ, elpr.getRhs()),
							new Bound(RelationSymbol.LEQ, elpr.getRhs()));
				} else {
					throw new AssertionError("unknown quantifier");
				}
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
				result.addSimpleBound(new Bound(elpr.getRelationSymbol(), elpr.getRhs()));
				break;
			default:
				throw new AssertionError("unknown relation symbol " + elpr.getRelationSymbol());
			}
		}
		return result;
	}

	private static TirBounds computeTirBoundForUnifiedLhs(final TermVariable eliminatee, final int quantifier,
			final ExplicitLhsPolynomialRelations elprs) {
		final TirBounds result = new TirBounds();
		Rational firstCoeffcient = null;
		Monomial firstMonomial = null;
		for (final ExplicitLhsPolynomialRelation elpr : elprs.getSimpleRelations()) {
			if (firstCoeffcient == null) {
				firstCoeffcient = elpr.getLhsCoefficient();
				assert firstMonomial == null;
				firstMonomial = elpr.getLhsMonomial();
			} else {
				if (!firstCoeffcient.equals(elpr.getLhsCoefficient()) || !firstMonomial.equals(elpr.getLhsMonomial())) {
					return null;
				}
			}
			final Bound bound = convertToBound(elpr);
			result.addSimpleBound(bound);
		}
		for (final Pair<ExplicitLhsPolynomialRelation, ExplicitLhsPolynomialRelation> pair : elprs.getAntiDerRelations()) {
			if (firstCoeffcient == null) {
				firstCoeffcient = pair.getFirst().getLhsCoefficient();
				assert firstMonomial == null;
				firstMonomial = pair.getFirst().getLhsMonomial();
			} else {
				if (!firstCoeffcient.equals(pair.getFirst().getLhsCoefficient()) || !firstMonomial.equals(pair.getFirst().getLhsMonomial())) {
					return null;
				}
			}
			final Bound lowerBound = convertToBound(pair.getFirst());
			final Bound upperBound = convertToBound(pair.getSecond());
			result.addAntiDerBound(lowerBound, upperBound);
		}
		return result;
	}

	private static Bound convertToBound(final ExplicitLhsPolynomialRelation elpr) throws AssertionError {
		final Bound bound;
		switch (elpr.getRelationSymbol()) {
		case DISTINCT:
		case EQ:
			throw new AssertionError("should have been handled before");
		case GEQ:
		case GREATER:
		case LEQ:
		case LESS:
			bound = new Bound(elpr.getRelationSymbol(), elpr.getRhs());
			break;
		default:
			throw new AssertionError("unknown relation symbol " + elpr.getRelationSymbol());
		}
		return bound;
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
					result.addAntiDerBound(new Bound(RelationSymbol.GREATER, solved.getRhs()),
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
					result.addAntiDerBound(new Bound(RelationSymbol.GEQ, solved.getRhs()),
							new Bound(RelationSymbol.LEQ, solved.getRhs()));
				} else {
					throw new AssertionError("unknown quantifier");
				}
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
				result.addSimpleBound(new Bound(solved.getRelationSymbol(), solved.getRhs()));
				break;
			default:
				throw new AssertionError("unknown relation symbol " + solved.getRelationSymbol());
			}
		}
		return result;
	}

	private static ExplicitLhsPolynomialRelations unifyByIntertibleDivision(final Script script, final TermVariable eliminatee,
			final Set<TermVariable> bannedForDivCapture, final int quantifier,
			final ExplicitLhsPolynomialRelations elprs) {
		final ExplicitLhsPolynomialRelations result = new ExplicitLhsPolynomialRelations();
		for (final ExplicitLhsPolynomialRelation elpr : elprs.getSimpleRelations()) {
			final ExplicitLhsPolynomialRelation solved = elpr.divInvertible(elpr.getLhsCoefficient());
			if (solved == null) {
				return null;
			} else {
				result.addSimpleRelation(solved);
			}
		}
		for (final Pair<ExplicitLhsPolynomialRelation, ExplicitLhsPolynomialRelation> pair : elprs.getAntiDerRelations()) {
			final ExplicitLhsPolynomialRelation solvedLower = pair.getFirst().divInvertible(pair.getFirst().getLhsCoefficient());
			final ExplicitLhsPolynomialRelation solvedUpper = pair.getSecond().divInvertible(pair.getSecond().getLhsCoefficient());
			if (solvedLower == null) {
				assert solvedUpper == null;
				return null;
			} else {
				if (pair.getFirst().getLhsCoefficient().isNegative()) {
					assert pair.getSecond().getLhsCoefficient().isNegative();
					// upper and lower have been swapped
					result.addAntiDerRelation(solvedUpper, solvedLower);
				} else {
					result.addAntiDerRelation(solvedLower, solvedUpper);
				}
			}

		}
		return result;
	}

	private static ExplicitLhsPolynomialRelations unifyByDivisionForInt(final Script script, final TermVariable eliminatee,
			final Set<TermVariable> bannedForDivCapture, final int quantifier,
			final ExplicitLhsPolynomialRelations elprs) {
		final ExplicitLhsPolynomialRelations result = new ExplicitLhsPolynomialRelations();
		for (final ExplicitLhsPolynomialRelation elpr : elprs.getSimpleRelations()) {
			final ExplicitLhsPolynomialRelation solved = divForInt(script, bannedForDivCapture, elpr);
			if (solved == null) {
				return null;
			} else {
				result.addSimpleRelation(solved);
			}
		}
		for (final Pair<ExplicitLhsPolynomialRelation, ExplicitLhsPolynomialRelation> pair : elprs.getAntiDerRelations()) {
			final ExplicitLhsPolynomialRelation solvedLower = divForInt(script, bannedForDivCapture, pair.getFirst());
			final ExplicitLhsPolynomialRelation solvedUpper = divForInt(script, bannedForDivCapture, pair.getSecond());
			if (solvedLower == null) {
				assert solvedUpper == null;
				return null;
			} else {
				if (pair.getFirst().getLhsCoefficient().isNegative()) {
					assert pair.getSecond().getLhsCoefficient().isNegative();
					// upper and lower have been swapped
					result.addAntiDerRelation(solvedUpper, solvedLower);
				} else {
					result.addAntiDerRelation(solvedLower, solvedUpper);
				}
			}

		}
		return result;
	}

	private static ExplicitLhsPolynomialRelation divForInt(final Script script,
			final Set<TermVariable> bannedForDivCapture, final ExplicitLhsPolynomialRelation elpr) {
		final Pair<ExplicitLhsPolynomialRelation, Term> pair = elpr.divideByIntegerCoefficient(script, bannedForDivCapture);
		if (pair == null) {
			return null;
		}
		if (pair.getSecond() != null) {
			throw new AssertionError("not this case");
		}
		return pair.getFirst();
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
				tmp = elpr.divInvertible(Rational.MONE);
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
					result.addAntiDerBound(
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
					result.addAntiDerBound(
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
			result.add(elpr.mul(factor, script, quantifier == QuantifiedFormula.EXISTS));
		}
		return result;
	}

	private static ExplicitLhsPolynomialRelations unifyByMultiplication(final Script script, final TermVariable eliminatee,
			final Set<TermVariable> bannedForDivCapture, final int quantifier,
			final ExplicitLhsPolynomialRelations elprs) {

		// lcm of absolute values of coefficients
		Rational lcm = Rational.ONE;
		for (final ExplicitLhsPolynomialRelation elpr : elprs.getSimpleRelations()) {
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
		for (final Pair<ExplicitLhsPolynomialRelation,ExplicitLhsPolynomialRelation> pair : elprs.getAntiDerRelations()) {
			final ExplicitLhsPolynomialRelation elpr = pair.getFirst();
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


		final ExplicitLhsPolynomialRelations result = new ExplicitLhsPolynomialRelations();
		for (final ExplicitLhsPolynomialRelation elpr : elprs.getSimpleRelations()) {
			final Rational factor = lcm.div(elpr.getLhsCoefficient());
			final ExplicitLhsPolynomialRelation solved = elpr.mul(factor, script, quantifier == QuantifiedFormula.EXISTS);
			if (solved == null) {
				return null;
			} else {
				result.addSimpleRelation(solved);
			}
		}
		for (final Pair<ExplicitLhsPolynomialRelation, ExplicitLhsPolynomialRelation> pair : elprs.getAntiDerRelations()) {
			final Rational factor = lcm.div(pair.getFirst().getLhsCoefficient());
			final ExplicitLhsPolynomialRelation solvedLower = pair.getFirst().mul(factor, script, quantifier == QuantifiedFormula.EXISTS);
			final ExplicitLhsPolynomialRelation solvedUpper = pair.getSecond().mul(factor, script, quantifier == QuantifiedFormula.EXISTS);
			if (solvedLower == null) {
				assert solvedUpper == null;
				return null;
			} else {
				if (pair.getFirst().getLhsCoefficient().isNegative()) {
					assert pair.getSecond().getLhsCoefficient().isNegative();
					// upper and lower have been swapped
					result.addAntiDerRelation(solvedUpper, solvedLower);
				} else {
					result.addAntiDerRelation(solvedLower, solvedUpper);
				}
			}

		}
		return result;
	}


	private static List<ExplicitLhsPolynomialRelation> convertOld(final List<Term> withEliminatee, final Script script,
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

	private static ExplicitLhsPolynomialRelations convert(final List<Term> withEliminatee, final Script script,
			final TermVariable eliminatee, final int quantifier) {
		final ExplicitLhsPolynomialRelations result = new ExplicitLhsPolynomialRelations();
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
			switch (elpr.getRelationSymbol()) {
			case GEQ:
			case GREATER:
			case LEQ:
			case LESS:
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
			case BVSGE:
			case BVSGT:
			case BVSLE:
			case BVSLT:
			case BVUGE:
			case BVUGT:
			case BVULE:
			case BVULT:
				throw new AssertionError("not implemented yet");
			default:
				throw new AssertionError("unknown relation " + elpr.getRelationSymbol());

			}
		}
		return result;
	}

	private static class ExplicitLhsPolynomialRelations {
		private final List<ExplicitLhsPolynomialRelation> mSimpleRelations = new ArrayList<>();
		private final List<Pair<ExplicitLhsPolynomialRelation, ExplicitLhsPolynomialRelation>> mAntiDerRelations = new ArrayList<>();

		void addSimpleRelation(final ExplicitLhsPolynomialRelation elpr) {
			mSimpleRelations.add(elpr);
		}

		void addAntiDerRelation(final ExplicitLhsPolynomialRelation lowerBound, final ExplicitLhsPolynomialRelation upperBound) {
			mAntiDerRelations.add(new Pair<ExplicitLhsPolynomialRelation, ExplicitLhsPolynomialRelation>(lowerBound, upperBound));
		}

		public List<ExplicitLhsPolynomialRelation> getSimpleRelations() {
			return mSimpleRelations;
		}

		public List<Pair<ExplicitLhsPolynomialRelation, ExplicitLhsPolynomialRelation>> getAntiDerRelations() {
			return mAntiDerRelations;
		}


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

		void addAntiDerBound(final Bound lowerBound, final Bound upperBound) {
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
			if (lowerBoundRelationSymbol.isRelationSymbolGE() && upperBoundRelationSymbol.isRelationSymbolLE()) {
				resultRelationSymbol = upperBoundRelationSymbol;
				if ((quantifier == QuantifiedFormula.FORALL) && SmtSortUtils.isIntSort(sort)) {
					offset = Rational.MONE;
				} else {
					offset = Rational.ZERO;
				}
			} else if ((lowerBoundRelationSymbol.isRelationSymbolGE() && upperBoundRelationSymbol.isRelationSymbolLT())
					|| (lowerBoundRelationSymbol.isRelationSymbolGT()
							&& upperBoundRelationSymbol.isRelationSymbolLE())) {
				if (quantifier == QuantifiedFormula.EXISTS) {
					resultRelationSymbol = upperBoundRelationSymbol.getStrictSymbol();
				} else if (quantifier == QuantifiedFormula.FORALL) {
					resultRelationSymbol = upperBoundRelationSymbol.getNonStrictSymbol();
				} else {
					throw new AssertionError("unknown quantifier");
				}
				offset = Rational.ZERO;
			} else if (lowerBoundRelationSymbol.isRelationSymbolGT() && upperBoundRelationSymbol.isRelationSymbolLT()) {
				resultRelationSymbol = upperBoundRelationSymbol;
				if ((quantifier == QuantifiedFormula.EXISTS) && SmtSortUtils.isIntSort(sort)) {
					offset = Rational.ONE;
				} else {
					offset = Rational.ZERO;
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
