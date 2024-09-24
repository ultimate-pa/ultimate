/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.ExtendedSimplificationResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryNumericRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.ExplicitLhsPolynomialRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.MultiCaseSolvedBinaryRelation.IntricateOperation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation.TransformInequality;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.SolveForSubjectUtils;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Transitive inequality resolution (TIR) for terms in XNF.
 *
 * @author Matthias Heizmann
 * @author Max Barth
 */
public class XnfTir extends XjunctPartialQuantifierElimination {

	private final XnfConversionTechnique mXnfConversionTechnique;

	public XnfTir(final ManagedScript script, final IUltimateServiceProvider services,
			final XnfConversionTechnique xnfConversionTechnique) {
		super(script, services);
		mXnfConversionTechnique = xnfConversionTechnique;
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
	public boolean resultIsXjunction() {
		return false;
	}

	public enum BoundType {
		UPPER, LOWER
	}

	@Override
	public Term[] tryToEliminate(final int quantifier, final Term[] inputConjuncts,
			final Set<TermVariable> eliminatees) {
		final Term inputConjunction = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier,
				Arrays.asList(inputConjuncts));
		List<Term> currentDisjuncts = new ArrayList<>(Arrays.asList(inputConjunction));
		final Iterator<TermVariable> it = eliminatees.iterator();
		while (it.hasNext()) {
			List<Term> nextDisjuncts = new ArrayList<>();
			final TermVariable eliminatee = it.next();
			if (!eliminatee.getSort().isNumericSort()) {
				// this technique is not applicable
				nextDisjuncts = currentDisjuncts;
				continue;
			}
			boolean unableToRemoveEliminatee = false;
			for (final Term oldDisjunct : currentDisjuncts) {
				final List<Term> elimResultDisjuncts = tryToEliminateSingleDisjuct(quantifier, oldDisjunct, eliminatee, eliminatees);
				if (elimResultDisjuncts == null) {
					// unable to eliminate
					unableToRemoveEliminatee = true;
					nextDisjuncts.add(oldDisjunct);
				} else {
					nextDisjuncts.addAll(elimResultDisjuncts);
				}
			}
			if (unableToRemoveEliminatee) {
				// not eliminated :-(
			} else {
				it.remove();
			}
			currentDisjuncts = nextDisjuncts;
		}
		final Term[] resultDisjuncts = currentDisjuncts.toArray(new Term[currentDisjuncts.size()]);
		final Term resultDisjunction = QuantifierUtils.applyCorrespondingFiniteConnective(mScript, quantifier,
				resultDisjuncts);
		//		final List<TermVariable> eliminateesAfter = eliminateesBefore.stream().filter(x -> !eliminatees.contains(x)).collect(Collectors.toList());
//		final String message = "Applied " + getAcronym() + " to " + inputConjuncts.length + " " +
//				QuantifierUtils.getNameOfDualJuncts(quantifier) + " and " + eliminateesBefore.size() + "eliminatees: " + eliminateesBefore +
//				" removed " + (eliminateesAfter.isEmpty() ? "nothing" : eliminateesAfter);
//		mLogger.info(message);
		return new Term[] { resultDisjunction };
	}

	private List<Term> tryToEliminateSingleDisjuct(final int quantifier, final Term disjunct,
			final TermVariable eliminatee, final Set<TermVariable> bannedForDivCapture) {
		final Term conjunction = tryToEliminateConjuncts(mServices, mScript, quantifier, disjunct, eliminatee, bannedForDivCapture);
		if (conjunction == null) {
			return null;
		}
		// Following lines used for debugging - remove them
		// Term term = SmtUtils.or(mScript, (Collection<Term>) result);
		// term = SmtUtils.simplify(mScript, term, mServices);
		// result =
		// Arrays.asList(PartialQuantifierElimination.getXjunctsOuter(quantifier,
		// term));
		//

		// TODO 2018-08-11 Matthias: Do not convert to XNF because this
		// will also affect all input xjuncts
		// In once introduced this as a workaround when the input was
		// already in XNF.
		Term disjunction;
		if (quantifier == QuantifiedFormula.EXISTS) {
			disjunction = SmtUtils.toDnf(mServices, mMgdScript, conjunction, mXnfConversionTechnique);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			disjunction = SmtUtils.toCnf(mServices, mMgdScript, conjunction, mXnfConversionTechnique);
		} else {
			throw new AssertionError("unknown quantifier");
		}
		assert !Arrays.asList(disjunction.getFreeVars()).contains(eliminatee) : "not eliminated";
		final ExtendedSimplificationResult simp = SmtUtils.simplifyWithStatistics(mMgdScript, conjunction, mServices,
				SimplificationTechnique.SIMPLIFY_DDA);
		disjunction = simp.getSimplifiedTerm();

		final List<Term> resultDisjunctions = Arrays.asList(QuantifierUtils.getCorrespondingFiniteJuncts(quantifier, disjunction));
		return resultDisjunctions;
	}

	public static Term tryToEliminateConjuncts(final IUltimateServiceProvider services, final Script script,
			final int quantifier, final Term disjunct, final TermVariable eliminatee,
			final Set<TermVariable> bannedForDivCapture) {
		final Term[] inputAtoms  = QuantifierUtils.getDualFiniteJuncts(quantifier, disjunct);
		final List<Term> termsWithoutEliminatee = new ArrayList<>();
		final List<Bound> upperBounds = new ArrayList<>();
		final List<Bound> lowerBounds = new ArrayList<>();
		final List<Pair<Term, Term>> antiDer = new ArrayList<>(); // TODO IDEE LISTE VON SolvedBinaryRelation

		for (final Term term : inputAtoms) {
			if (!Arrays.asList(term.getFreeVars()).contains(eliminatee)) {
				termsWithoutEliminatee.add(term);
			} else {
				TransformInequality transform;
				if (quantifier == QuantifiedFormula.EXISTS) {
					transform = TransformInequality.STRICT2NONSTRICT;
				} else if (quantifier == QuantifiedFormula.FORALL) {
					transform = TransformInequality.NONSTRICT2STRICT;
				} else {
					throw new AssertionError("unknown quantifier");
				}
				final PolynomialRelation polyRel = PolynomialRelation.of(script, term, transform);
				if (polyRel == null) {
					// no chance to eliminate the variable
					return null;
				}
				if (!polyRel.isVariable(eliminatee)) {
					// eliminatee occurs probably only in select
					return null;
				}

				SolvedBinaryRelation sbr = polyRel.solveForSubject(script, eliminatee);
				final boolean divByIntegerConstant;
				if (sbr == null) {
					final ExplicitLhsPolynomialRelation elpr = ExplicitLhsPolynomialRelation.moveMonomialToLhs(script,
							eliminatee, polyRel);
					if (elpr == null) {
						return null;
					}
					if (!SmtSortUtils.isIntSort(eliminatee.getSort())) {
						return null;
					}
					final Pair<ExplicitLhsPolynomialRelation, Term> pair = elpr.divideByIntegerCoefficient(script,
							bannedForDivCapture);
					if (pair == null) {
						return null;
					} else {
						final ExplicitLhsPolynomialRelation tmp = pair.getFirst();
						if (!tmp.getLhsMonomial().isLinear()) {
							return null;
						}
						sbr = new SolvedBinaryRelation(tmp.getLhsMonomial().getSingleVariable(),
								tmp.getRhs().toTerm(script), tmp.getRelationSymbol(),
								IntricateOperation.DIV_BY_INTEGER_CONSTANT);
						divByIntegerConstant = true;
					}
				} else {
					divByIntegerConstant = false;
				}
				// TODO: This check is done above and hence obsolete (check this before you
				// delete code)
				if (SolveForSubjectUtils.isVariableDivCaptured(sbr, bannedForDivCapture)) {
					throw new AssertionError("should not be possible to divCapture here");
				}
				//				if (!sbr.getAssumptionsMap().isEmpty()
//						&& !sbr.getRelationSymbol().equals(RelationSymbol.DISTINCT)
//						&& !sbr.getRelationSymbol().equals(RelationSymbol.EQ)) {
//					return null;
//				}
				final Term eliminateeOnLhs = sbr.toTerm(script);
				final BinaryNumericRelation bnr = BinaryNumericRelation.convert(eliminateeOnLhs);
				switch (bnr.getRelationSymbol()) {
				case DISTINCT:
					if (quantifier == QuantifiedFormula.EXISTS) {
						if (divByIntegerConstant) {
							antiDer.add(antiDerWithAssumption(script, QuantifiedFormula.EXISTS, term, eliminatee));
						} else {
							antiDer.add(new Pair<Term, Term>(bnr.getRhs(), bnr.getRhs()));
						}
					} else {
						assert occursInsideSelectTerm(script, term, eliminatee) : "should have been removed by DER";
						// no chance to eliminate the variable
						throw new AssertionError("should have been removed by DER");
					}
					break;
				case EQ:
					if (quantifier == QuantifiedFormula.FORALL) {
						if (divByIntegerConstant) {
							antiDer.add(antiDerWithAssumption(script, QuantifiedFormula.FORALL, term, eliminatee));
						} else {
							antiDer.add(new Pair<Term, Term>(bnr.getRhs(), bnr.getRhs()));
						}
					} else {
						assert occursInsideSelectTerm(script, term, eliminatee) : "should have been removed by DER";
						// no chance to eliminate the variable
						throw new AssertionError("should have been removed by DER");
					}
					break;
				case GEQ:
					lowerBounds.add(new Bound(false, bnr.getRhs()));
					break;
				case GREATER:
					lowerBounds.add(new Bound(true, bnr.getRhs()));
					break;
				case LEQ:
					upperBounds.add(new Bound(false, bnr.getRhs()));
					break;
				case LESS:
					upperBounds.add(new Bound(true, bnr.getRhs()));
					break;
				default:
					throw new AssertionError();
				}
			}
		}
		final AntiDerBuildingInstructions bi = new XnfTir.AntiDerBuildingInstructions(services, script, quantifier, upperBounds, lowerBounds, antiDer);
		final List<Term> resultAtoms = new ArrayList<>();
		for (final Bound lowerBound : lowerBounds) {
			for (final Bound upperBound : upperBounds) {
				resultAtoms.add(buildInequality(script, quantifier, lowerBound, upperBound));
				if (!services.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(XnfTir.class,
							"building " + lowerBounds.size() * upperBounds.size() + " inequalities");
				}
			}
		}
		resultAtoms.addAll(termsWithoutEliminatee);
		if (!antiDer.isEmpty()) {
			resultAtoms.add(bi.buildCorrespondingFiniteJunction());
		}
		final Term result = QuantifierUtils.applyDualFiniteConnective(script, quantifier, resultAtoms);
		assert !Arrays.asList(result.getFreeVars()).contains(eliminatee) : "not eliminated";
		return result;
	}



	/**
	 * transforms
	 * (a != b) to (a < b OR a > b) for exist quantifier and
	 * (a = b) to (a <= b OR a >= b) for forall quantifier
	 * uses solveForSubject on both disjuncts to get the right hand side of the both relations.
	 * returns lower/upper bound right hand side.
	 */
	private static Pair<Term, Term> antiDerWithAssumption(final Script script, final int quantifier,
			final Term originalTerm, final Term eliminatee) {

		final Rational coeff;
		{
			final PolynomialRelation origPolyRel = PolynomialRelation.of(script, originalTerm);
			final ExplicitLhsPolynomialRelation elpr = ExplicitLhsPolynomialRelation.moveMonomialToLhs(script,
					eliminatee, origPolyRel);
			coeff = elpr.getLhsCoefficient();
		}

		// Strict to NONStrict transformation is done in the method "computeBound"
		final TransformInequality transform = TransformInequality.NO_TRANFORMATION;
		RelationSymbol lowerRelationSymbol;
		RelationSymbol upperRelationSymbol;
		if (quantifier == QuantifiedFormula.EXISTS) {
			if (coeff.isNegative()) {
				// relation symbol will be swapped by division
				lowerRelationSymbol = RelationSymbol.LESS;
				upperRelationSymbol = RelationSymbol.GREATER;
			} else {
				lowerRelationSymbol = RelationSymbol.GREATER;
				upperRelationSymbol = RelationSymbol.LESS;
			}
		} else {
			if (coeff.isNegative()) {
				// relation symbol will be swapped by division
				lowerRelationSymbol = RelationSymbol.LEQ;
				upperRelationSymbol = RelationSymbol.GEQ;
			} else {
				lowerRelationSymbol = RelationSymbol.GEQ;
				upperRelationSymbol = RelationSymbol.LEQ;
			}
		}
		final BinaryNumericRelation bnr = BinaryNumericRelation.convert(originalTerm);

		final BinaryNumericRelation lowerBoundBnr = bnr.changeRelationSymbol(lowerRelationSymbol);
		final PolynomialRelation relLower = PolynomialRelation.of(script, lowerBoundBnr.toTerm(script), transform);
		final ExplicitLhsPolynomialRelation elprLower = ExplicitLhsPolynomialRelation.moveMonomialToLhs(script,
				eliminatee, relLower);
		assert(coeff.equals(elprLower.getLhsCoefficient()));
		// TODO use bannedforDivCapture
		final SolvedBinaryRelation sbrLower = elprLower.divideByIntegerCoefficientForInequalities(script,
				Collections.emptySet());

		final BinaryNumericRelation upperBoundBnr = bnr.changeRelationSymbol(upperRelationSymbol);
		final PolynomialRelation relUpper = PolynomialRelation.of(script, upperBoundBnr.toTerm(script), transform);
		final ExplicitLhsPolynomialRelation elprUpper = ExplicitLhsPolynomialRelation.moveMonomialToLhs(script,
				eliminatee, relUpper);
		assert(coeff.equals(elprUpper.getLhsCoefficient()));
		// TODO use bannedforDivCapture
		final SolvedBinaryRelation sbrUpper = elprUpper.divideByIntegerCoefficientForInequalities(script,
				Collections.emptySet());

		if ((sbrLower == null) || (sbrUpper == null)) {
			throw new AssertionError("suddenly unsolvable");
		}
		final Term lowerBound = sbrLower.getRightHandSide();
		final Term upperBound = sbrUpper.getRightHandSide();
		return new Pair<Term, Term>(lowerBound, upperBound);
	}

	/**
	 * @return true iff tv is subterm of some select term in term.
	 */
	private static boolean occursInsideSelectTerm(Script script, final Term term, final TermVariable tv) {
		final List<MultiDimensionalSelect> selectTerms = MultiDimensionalSelect.extractSelectShallow(term);
		for (final MultiDimensionalSelect mds : selectTerms) {
			for (final Term index : mds.getIndex()) {
				if (Arrays.asList(index.getFreeVars()).contains(tv)) {
					return true;
				}
			}
			if (Arrays.asList(mds.toTerm(script).getFreeVars()).contains(tv)) {
				return true;
			}
			if (Arrays.asList(mds.getArray().getFreeVars()).contains(tv)) {
				return true;
			}
		}
		return false;
	}


	private static Term buildInequality(final Script script, final int quantifier, final Bound lowerBound,
			final Bound upperBound) {
		final boolean isStrict;
		final boolean lbIsInt = SmtSortUtils.isIntSort(lowerBound.getTerm().getSort());
		if (quantifier == QuantifiedFormula.EXISTS) {
			isStrict = lowerBound.isIsStrict() || upperBound.isIsStrict();
			assert !(lowerBound.isIsStrict() && upperBound.isIsStrict())
					|| !lbIsInt : "unsound if int and both are strict";
		} else if (quantifier == QuantifiedFormula.FORALL) {
			isStrict = lowerBound.isIsStrict() && upperBound.isIsStrict();
			assert !(!lowerBound.isIsStrict() && !upperBound.isIsStrict())
					|| !lbIsInt : "unsound if int and both are non-strict";
		} else {
			throw new AssertionError("unknown quantifier");
		}
		final String symbol = isStrict ? "<" : "<=";
		final Term term = script.term(symbol, lowerBound.getTerm(), upperBound.getTerm());
		final PolynomialRelation polyRel = PolynomialRelation.of(script, term);
		if (polyRel == null) {
			throw new AssertionError("should be affine");
		}
		return polyRel.toTerm(script);
	}

	private static class AntiDerBuildingInstructions {
		private final IUltimateServiceProvider mServices;
		private final Script mScript;
		private final int mQuantifier;
		private final List<Bound> mUpperBounds;
		private final List<Bound> mLowerBounds;
		private final List<Pair<Term, Term>> mAntiDer;

		public AntiDerBuildingInstructions(final IUltimateServiceProvider services, final Script script, final int quantifier,
				final List<Bound> upperBounds, final List<Bound> lowerBounds, final List<Pair<Term, Term>> antiDer) {
			super();
			mServices = services;
			mScript = script;
			mQuantifier = quantifier;
			mUpperBounds = upperBounds;
			mLowerBounds = lowerBounds;
			mAntiDer = antiDer;
		}

		Term buildCorrespondingFiniteJunction() {
			final ArrayList<Term> resultCorrespondingFiniteJuncts = new ArrayList<>();
			for (int i = 0; i < Math.pow(2, mAntiDer.size()); i++) {
				final ArrayList<Term> resultAtoms = new ArrayList<>();
				final ArrayList<Bound> adLowerBounds = new ArrayList<>();
				final ArrayList<Bound> adUpperBounds = new ArrayList<>();
				for (int k = 0; k < mAntiDer.size(); k++) {
					// zero means lower - one means upper
					if (BigInteger.valueOf(i).testBit(k)) {
						final Bound upperBound = computeBound(mAntiDer.get(k).getSecond(), mQuantifier,
								BoundType.UPPER);
						adUpperBounds.add(upperBound);
					} else {
						final Bound lowerBound = computeBound(mAntiDer.get(k).getFirst(), mQuantifier, BoundType.LOWER);
						adLowerBounds.add(lowerBound);

					}
				}

				for (final Bound adLower : adLowerBounds) {
					for (final Bound adUpper : adUpperBounds) {
						resultAtoms.add(buildInequality(mScript, mQuantifier, adLower, adUpper));
					}
					for (final Bound upperBound : mUpperBounds) {
						resultAtoms.add(buildInequality(mScript, mQuantifier, adLower, upperBound));
					}
				}
				for (final Bound adUpper : adUpperBounds) {
					for (final Bound lowerBound : mLowerBounds) {
						resultAtoms.add(buildInequality(mScript, mQuantifier, lowerBound, adUpper));
					}
				}
				resultCorrespondingFiniteJuncts.add(QuantifierUtils.applyDualFiniteConnective(mScript, mQuantifier, resultAtoms));
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(this.getClass(),
							"building " + Math.pow(2, mAntiDer.size()) + " xjuncts");
				}
			}
			return QuantifierUtils.applyCorrespondingFiniteConnective(mScript, mQuantifier, resultCorrespondingFiniteJuncts);
		}


		private Bound computeBound(final Term term, final int quantifier, final BoundType boundType) {
			final Bound result;
			if (SmtSortUtils.isRealSort(term.getSort())) {
				if (quantifier == QuantifiedFormula.EXISTS) {
					return new Bound(true, term);
				} else if (quantifier == QuantifiedFormula.FORALL) {
					return new Bound(false, term);
				} else {
					throw new AssertionError("unknown quantifier");
				}
			} else if (SmtSortUtils.isIntSort(term.getSort())) {
				final Term one = SmtUtils.constructIntValue(mScript, BigInteger.ONE);
				if (quantifier == QuantifiedFormula.EXISTS) {
					// transform terms such that
					// lower < x /\ x < upper
					// becomes
					// lower+1 <= x /\ x <= upper-1
					if (boundType == BoundType.LOWER) {
						result = new Bound(false, mScript.term("+", term, one));
					} else if (boundType == BoundType.UPPER) {
						result = new Bound(false, mScript.term("-", term, one));
					} else {
						throw new AssertionError("unknown BoundType" + boundType);
					}
				} else if (quantifier == QuantifiedFormula.FORALL) {
					// transform terms such that
					// lower <= x \/ x <= upper becomes
					// lower-1 < x \/ x < upper+1
					if (boundType == BoundType.LOWER) {
						result = new Bound(true, mScript.term("-", term, one));
					} else if (boundType == BoundType.UPPER) {
						result = new Bound(true, mScript.term("+", term, one));
					} else {
						throw new AssertionError("unknown BoundType" + boundType);
					}
				} else {
					throw new AssertionError("unknown quantifier");
				}
			} else {
				throw new AssertionError("unknown sort " + term.getSort());
			}
			return result;
		}

	}

	private static class Bound {
		private final boolean mIsStrict;
		private final Term mTerm;

		public Bound(final boolean isStrict, final Term term) {
			super();
			mIsStrict = isStrict;
			mTerm = term;
		}

		public boolean isIsStrict() {
			return mIsStrict;
		}

		public Term getTerm() {
			return mTerm;
		}

		@Override
		public String toString() {
			return "Bound [mIsStrict=" + mIsStrict + ", mTerm=" + mTerm + "]";
		}
	}




}
