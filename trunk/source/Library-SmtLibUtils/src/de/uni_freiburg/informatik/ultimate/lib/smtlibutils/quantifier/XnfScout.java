/*
 * Copyright (C) 2019-2022 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019-2022 University of Freiburg
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryEqualityRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.MultiCaseSolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TreeHashRelation;

/**
 * Computes an estimation of a formula's size if we apply our algorithm for the
 * elimination of quantifiers.<br>
 * Our algorithm (see {@link QuantifierPushTermWalker}) handles existentially
 * quantified disjunctions by pushing ∃ over ∨ and it handles existentially
 * quantified conjunctions by applying our "elimination techniques" (see
 * {@link DualJunctionQuantifierElimination}) to these kinds of terms. If the
 * elimination techniques fail and some conjunct is a disjunction we rewrite
 * according to the and-or distributivity rule, push ∃ over ∨ and recurse on the
 * disjuncts.<br>
 * Here an interesting questions are
 * <li>with which eliminatee(s) should we start with
 * <li>which conjunct should we pick for the application of the distributivity
 * rule. The algorithms implemented in this class try to explore (hence the name
 * scout) the effect of these choices in advance. The measure that we use is the
 * expected size of the formula. For the size we count the the number of
 * existentially quantified disjuncts and we count separately whether the
 * quantifier can be eliminated.<br>
 * Usually we get a very coarse overapproximation, since eliminations typically
 * allow simplifications that reduce the size of the formula significantly.
 * However, this is not always an overapproximation. Some eliminations (e.g.,
 * TIR for ≠) introduce new disjunctions themselves. <br>
 * TODO 20220706 Matthias:
 * <li>Add support for {@link MultiCaseSolvedBinaryRelation}s but make sure that
 * variables quantified in ancestors are considered as blockers for divisiblity
 * constraints.
 * <li>Improve array heuristic. We incorrectly assume that all arrays have to
 * occur below the root level (quantifier). This may however compensate the huge
 * blowup that the array elimination sometimes brings.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class XnfScout extends CondisTermTransducer<XnfScout.Result> {

	public enum Adk {
		ATOM, DISJUNCTION, CONJUNCTION
	}

	public enum Occurrence {
		/**
		 * Eliminatee occurs DER eliminable in conjunction. This is great because it is
		 * still eliminable if we add more conjunct.
		 */
		DER,
		/**
		 * Eliminatee is not DER eliminable in conjunction but occurs eliminable in
		 * every conjunct (e.g. eliminable via TIR).
		 */
		ELIMINABLE,
		/**
		 * Eliminatee is not eliminable in at least on conjunct.
		 */
		OTHER_OCCURRENCE,
		/**
		 * Eliminatee does not occur in this conjunction.
		 */
		ABSENT
	}

	/**
	 * Yet probably not fully matured optimization based on the following
	 * observation: If we have a term of the form `∃x.F[x] ∧ (x=t V G[x])` our
	 * algorithm presumes that we have to bring F into DNF. This is typically only
	 * true for the combination of F and G, for the combination of `x=t` and F we
	 * can avoid to bring F in DNF since we can apply DER directly. This
	 * optimization is however only a workaround: The idea is that we combine a DER
	 * term only with the original terms (before DNF conversion) of the other
	 * conjunct. If the other conjunct however also contains DER disjuncts it is
	 * difficult to count the number of the DER-applicable disjuncts since we don't
	 * know how DER-applicable disjuncts after DNF and the original disjuncts are
	 * related. (The result probably depends on the order in which we descend into
	 * the conjuncts.) Nonetheless, I think this optimization is a good idea.
	 * However an quick evaluation on 20220710 did not show that the optimization
	 * helps.
	 */
	private static final boolean OPTION_OMIT_DESCED_FOR_DER = false;

	private final Script mScript;
	private final int mQuantifier;
	private final TermVariable mEliminatee;
	private final Set<TermVariable> mQuantifiedInAncestors;

	public XnfScout(final Script script, final int quantifier, final TermVariable eliminatee,
			final Set<TermVariable> quantifiedInAncestors) {
		super();
		mScript = script;
		mQuantifier = quantifier;
		mEliminatee = eliminatee;
		mQuantifiedInAncestors = quantifiedInAncestors;
	}

	private Occurrence classify(final Script script, final int quantifier, final Term term,
			final TermVariable eliminatee, final Set<TermVariable> quantifiedInAncestors) {
		if (!Arrays.asList(term.getFreeVars()).contains(eliminatee)) {
			return Occurrence.ABSENT;
		}
		if (SmtSortUtils.isBoolSort(eliminatee.getSort())) {
			if (term.equals(eliminatee) || eliminatee.equals(SmtUtils.unzipNot(term))) {
				return Occurrence.DER;
			} else {
				return Occurrence.OTHER_OCCURRENCE;
			}
		} else if (SmtSortUtils.isArraySort(eliminatee.getSort())) {
			if (isDerRelationForArray(quantifier, term, eliminatee)) {
				return Occurrence.DER;
			} else {
				// For simplicity we assume that the array variable is always eliminable. This
				// is however not true if the array is, e.g., the parameter of a function symbol
				// or the index of another array.
				return Occurrence.ELIMINABLE;
			}
		} else {
			final PolynomialRelation polyRel = PolynomialRelation.of(script, term);
			if (polyRel == null) {
				return Occurrence.OTHER_OCCURRENCE;
			}
			final SolvedBinaryRelation sbr = polyRel.solveForSubject(script, eliminatee);
			if (sbr == null) {
				return Occurrence.OTHER_OCCURRENCE;
			}
			if (polyRel.getRelationSymbol() == QuantifierUtils.getDerOperator(quantifier)) {
				return Occurrence.DER;
			} else {
				return Occurrence.ELIMINABLE;
			}
		}
	}

	private boolean isDerRelationForArray(final int quantifier, final Term term, final TermVariable eliminatee) {
		final BinaryEqualityRelation ber = BinaryEqualityRelation.convert(term);
		if (ber == null) {
			return false;
		}
		final SolvedBinaryRelation sbr = ber.solveForSubject(null, eliminatee);
		if (sbr == null) {
			return false;
		}
		return (ber.getRelationSymbol() == QuantifierUtils.getDerOperator(quantifier));
	}

	@Override
	protected Result transduceAtom(final Term term) {
		final long derCorrespondingJuncts;
		final long eliminableCorrespondingJuncts;
		final long occurringCorrespondingJuncts;
		final boolean atLeastOneNonInvolvedCorrespondingJunct;
		final Occurrence classification = classify(mScript, mQuantifier, term, mEliminatee, mQuantifiedInAncestors);
		switch (classification) {
		case ABSENT:
			derCorrespondingJuncts = 0;
			eliminableCorrespondingJuncts = 0;
			occurringCorrespondingJuncts = 0;
			atLeastOneNonInvolvedCorrespondingJunct = true;
			break;
		case DER:
			derCorrespondingJuncts = 1;
			eliminableCorrespondingJuncts = 0;
			occurringCorrespondingJuncts = 0;
			atLeastOneNonInvolvedCorrespondingJunct = false;
			break;
		case ELIMINABLE:
			derCorrespondingJuncts = 0;
			eliminableCorrespondingJuncts = 1;
			occurringCorrespondingJuncts = 0;
			atLeastOneNonInvolvedCorrespondingJunct = false;
			break;
		case OTHER_OCCURRENCE:
			derCorrespondingJuncts = 0;
			eliminableCorrespondingJuncts = 0;
			occurringCorrespondingJuncts = 1;
			atLeastOneNonInvolvedCorrespondingJunct = false;
			break;
		default:
			throw new AssertionError("unknown value: " + classification);
		}
		return new Result(Adk.ATOM, derCorrespondingJuncts, eliminableCorrespondingJuncts, occurringCorrespondingJuncts,
				atLeastOneNonInvolvedCorrespondingJunct);
	}

	@Override
	protected Result transduceConjunction(final ApplicationTerm originalTerm, final List<Result> transducedArguments) {
		final Result result;
		if (mQuantifier == QuantifiedFormula.EXISTS) {
			result = transduceDual(originalTerm, Adk.CONJUNCTION, transducedArguments);
		} else if (mQuantifier == QuantifiedFormula.FORALL) {
			result = transduceCorresponding(originalTerm, Adk.CONJUNCTION, transducedArguments);
		} else {
			throw new AssertionError("Unknown quantifier " + mQuantifier);
		}
		return result;
	}

	private Result transduceCorresponding(final ApplicationTerm originalTerm, final Adk adk,
			final List<Result> transducedArguments) {
		double derCorrespondingJuncts = 0;
		double eliminableCorrespondingJuncts = 0;
		double occurringCorrespondingJuncts = 0;
		boolean atLeastOneNonInvolvedCorrespondingJunct = false;
		for (final Result arg : transducedArguments) {
			if (arg.getAdk() == adk) {
				throw new AssertionError("Expected alternation between conjunction and disjunction");
			}
			derCorrespondingJuncts += arg.getDerCorrespondingJuncts();
			eliminableCorrespondingJuncts += arg.getEliminableCorrespondingJuncts();
			occurringCorrespondingJuncts += arg.getOccurringCorrespondingJuncts();
			atLeastOneNonInvolvedCorrespondingJunct |= arg.isAtLeastOneNonInvolvedCorrespondingJunct();
		}
		return new Result(adk, derCorrespondingJuncts, eliminableCorrespondingJuncts, occurringCorrespondingJuncts,
				atLeastOneNonInvolvedCorrespondingJunct);
	}

	private Result transduceDual(final ApplicationTerm originalTerm, final Adk adk,
			final List<Result> transducedArguments) {
		double originalCorrespondingJuncts = QuantifierUtils.getCorrespondingFiniteJuncts(mQuantifier,
				originalTerm.getParameters()[0]).length;
		double derCorrespondingJuncts = transducedArguments.get(0).getDerCorrespondingJuncts();
		double eliminableCorrespondingJuncts = transducedArguments.get(0).getEliminableCorrespondingJuncts();
		double occurringCorrespondingJuncts = transducedArguments.get(0).getOccurringCorrespondingJuncts();
		boolean atLeastOneNonInvolvedCorrespondingJunct = transducedArguments.get(0)
				.isAtLeastOneNonInvolvedCorrespondingJunct();
		for (int i = 1; i < transducedArguments.size(); i++) {
			if (transducedArguments.get(i).getAdk() == adk) {
				throw new AssertionError("Expected alternation between conjunction and disjunction");
			}
			final double oldOriginalCorrespondingJuncts = originalCorrespondingJuncts;
			final double oldDerCorrespondingJuncts = derCorrespondingJuncts;
			final double oldEliminableCorrespondingJuncts = eliminableCorrespondingJuncts;
			final double oldEccurringCorrespondingJuncts = occurringCorrespondingJuncts;
			final double oldNonInvolved = (atLeastOneNonInvolvedCorrespondingJunct ? 1 : 0);

			final double operandOriginalCorrespondingJuncts = QuantifierUtils
					.getCorrespondingFiniteJuncts(mQuantifier, originalTerm.getParameters()[i]).length;
			final double operandDerCorrespondingJuncts = transducedArguments.get(i).getDerCorrespondingJuncts();
			final double operandEliminableCorrespondingJuncts = transducedArguments.get(i)
					.getEliminableCorrespondingJuncts();
			final double operandOccurringCorrespondingJuncts = transducedArguments.get(i)
					.getOccurringCorrespondingJuncts();
			final double operandNonInvolved = (transducedArguments.get(i).isAtLeastOneNonInvolvedCorrespondingJunct()
					? 1
					: 0);
			originalCorrespondingJuncts = oldOriginalCorrespondingJuncts * operandOriginalCorrespondingJuncts;
			if (OPTION_OMIT_DESCED_FOR_DER) {
				derCorrespondingJuncts = oldDerCorrespondingJuncts * operandOriginalCorrespondingJuncts
						+ operandDerCorrespondingJuncts * oldOriginalCorrespondingJuncts
						- derCorrespondingJuncts * operandDerCorrespondingJuncts;
			} else {
				derCorrespondingJuncts = oldDerCorrespondingJuncts * operandDerCorrespondingJuncts
						+ oldDerCorrespondingJuncts * operandEliminableCorrespondingJuncts
						+ oldDerCorrespondingJuncts * operandOccurringCorrespondingJuncts
						+ oldDerCorrespondingJuncts * operandNonInvolved
						+ oldEliminableCorrespondingJuncts * operandDerCorrespondingJuncts
						+ oldEccurringCorrespondingJuncts * operandDerCorrespondingJuncts
						+ oldNonInvolved * operandDerCorrespondingJuncts;
			}
			occurringCorrespondingJuncts = oldEccurringCorrespondingJuncts * operandEliminableCorrespondingJuncts
					+ oldEccurringCorrespondingJuncts * operandOccurringCorrespondingJuncts
					+ oldEccurringCorrespondingJuncts * operandNonInvolved
					+ oldEliminableCorrespondingJuncts * operandOccurringCorrespondingJuncts
					+ oldNonInvolved * operandOccurringCorrespondingJuncts;
			eliminableCorrespondingJuncts = oldEliminableCorrespondingJuncts * operandEliminableCorrespondingJuncts
					+ oldEliminableCorrespondingJuncts * operandNonInvolved
					+ oldNonInvolved * operandEliminableCorrespondingJuncts;
			atLeastOneNonInvolvedCorrespondingJunct &= transducedArguments.get(i)
					.isAtLeastOneNonInvolvedCorrespondingJunct();
		}
		return new Result(adk, derCorrespondingJuncts, eliminableCorrespondingJuncts, occurringCorrespondingJuncts,
				atLeastOneNonInvolvedCorrespondingJunct);
	}

	@Override
	protected Result transduceDisjunction(final ApplicationTerm originalTerm, final List<Result> transducedArguments) {
		final Result result;
		if (mQuantifier == QuantifiedFormula.EXISTS) {
			result = transduceCorresponding(originalTerm, Adk.DISJUNCTION, transducedArguments);
		} else if (mQuantifier == QuantifiedFormula.FORALL) {
			result = transduceDual(originalTerm, Adk.DISJUNCTION, transducedArguments);
		} else {
			throw new AssertionError("Unknown quantifier " + mQuantifier);
		}
		return result;

	}

	/**
	 * Estimate on the eliminability of an eliminatee. See
	 * {@link XnfScout#Occurrence}.
	 */
	public static class Result implements Comparable<Result> {
		private final Adk mAdk;
		private final boolean mAtLeastOneNonInvolvedCorrespondingJunct;
		private final double mDerCorrespondingJuncts;
		private final double mEliminableCorrespondingJuncts;
		private final double mOccurringCorrespondingJuncts;

		public Result(final Adk adk, final double derCorrespondingJuncts, final double eliminableCorrespondingJuncts,
				final double occurringCorrespondingJuncts, final boolean atLeastOneNonInvolvedCorrespondingJunct) {
			super();
			mAdk = adk;
			mAtLeastOneNonInvolvedCorrespondingJunct = atLeastOneNonInvolvedCorrespondingJunct;
			mDerCorrespondingJuncts = derCorrespondingJuncts;
			mEliminableCorrespondingJuncts = eliminableCorrespondingJuncts;
			mOccurringCorrespondingJuncts = occurringCorrespondingJuncts;
		}

		public Adk getAdk() {
			return mAdk;
		}

		public boolean isAtLeastOneNonInvolvedCorrespondingJunct() {
			return mAtLeastOneNonInvolvedCorrespondingJunct;
		}

		public double getDerCorrespondingJuncts() {
			return mDerCorrespondingJuncts;
		}

		public double getEliminableCorrespondingJuncts() {
			return mEliminableCorrespondingJuncts;
		}

		public double getOccurringCorrespondingJuncts() {
			return mOccurringCorrespondingJuncts;
		}

		@Override
		public String toString() {
			return String.format("%s: %s DER, %s eliminable, %s other occurring, %s non-involved", mAdk,
					mDerCorrespondingJuncts, mEliminableCorrespondingJuncts, mOccurringCorrespondingJuncts,
					mAtLeastOneNonInvolvedCorrespondingJunct);
		}

		@Override
		public int compareTo(final Result other) {
			{
				final int step1 = Double.valueOf(getOccurringCorrespondingJuncts())
						.compareTo(Double.valueOf(other.getOccurringCorrespondingJuncts()));
				if (step1 != 0) {
					return step1;
				}
			}
			{
				final int step2 = Double.valueOf(getEliminableCorrespondingJuncts())
						.compareTo(Double.valueOf(other.getEliminableCorrespondingJuncts()));
				if (step2 != 0) {
					return step2;
				}
			}
			{
				final int step3 = Double.valueOf(getDerCorrespondingJuncts())
						.compareTo(Double.valueOf(other.getDerCorrespondingJuncts()));
				if (step3 != 0) {
					return step3;
				}
			}
			{
				final int step4 = Boolean.valueOf(isAtLeastOneNonInvolvedCorrespondingJunct())
						.compareTo(Boolean.valueOf(other.isAtLeastOneNonInvolvedCorrespondingJunct()));
				if (step4 != 0) {
					return step4;
				}
			}
			return 0;
		}

		public Double computeDerRatio() {
			final Double all = (getDerCorrespondingJuncts() + getEliminableCorrespondingJuncts()
					+ getOccurringCorrespondingJuncts() + (isAtLeastOneNonInvolvedCorrespondingJunct() ? 1 : 0));
			final Double derRatio = (getDerCorrespondingJuncts()) / all;
			return derRatio;
		}

		public Double computeEliminableRatio() {
			final Double all = (getDerCorrespondingJuncts() + getEliminableCorrespondingJuncts()
					+ getOccurringCorrespondingJuncts() + (isAtLeastOneNonInvolvedCorrespondingJunct() ? 1 : 0));
			final Double eliminableRatio = (getEliminableCorrespondingJuncts()) / all;
			return eliminableRatio;
		}
	}

	/**
	 * Heuristic for selecting an eliminatee that preferably can be eliminated and
	 * that can be eliminated with a preferably small blowup of the formula's size.
	 */
	public static TermVariable selectBestEliminatee(final Script script, final int quantifier,
			final List<TermVariable> eliminatees, final List<Term> dualFiniteParams) {
		if (eliminatees.size() == 1) {
			return eliminatees.iterator().next();
		}
		final Map<TermVariable, XnfScout.Result> score = computeApplicabilityScore(script, quantifier, eliminatees,
				dualFiniteParams);
		final TreeHashRelation<XnfScout.Result, TermVariable> tr = new TreeHashRelation<>();
		tr.reverseAddAll(score);
		final Map.Entry<XnfScout.Result, HashSet<TermVariable>> best = tr.entrySet().iterator().next();
		return best.getValue().iterator().next();
	}

	private static Map<TermVariable, XnfScout.Result> computeApplicabilityScore(final Script script,
			final int quantifier, final List<TermVariable> eliminatees, final List<Term> currentDualFiniteParams) {
		final Term correspondingFiniteJunction = QuantifierUtils.applyDualFiniteConnective(script, quantifier,
				currentDualFiniteParams);
		final Map<TermVariable, XnfScout.Result> result = new HashMap<>();
		for (final TermVariable eliminatee : eliminatees) {
			final XnfScout.Result score = new XnfScout(script, quantifier, eliminatee, null)
					.transduce(correspondingFiniteJunction);
			result.put(eliminatee, score);
		}
		return result;
	}

	/**
	 * Recommend the conjunct (resp. disjunct for universal quantification) that we
	 * should pick for applying the and-or distributivity rule.
	 *
	 */
	public static int computeRecommendation(final Script script, final Set<TermVariable> eliminatees,
			final Term[] dualFiniteParams, final int quantifier) {
		int res = computeRecommendationDer(script, eliminatees, dualFiniteParams, quantifier);
		if (res == -1) {
			res = computeRecommendationEliminable(script, eliminatees, dualFiniteParams, quantifier);
		}
		return res;
	}

	public static int computeRecommendation(final Script script, final Set<TermVariable> eliminatees,
			final Term[] dualFiniteParams, final int quantifier, final Function<Result, Double> ratioProvider) {
		final List<Double> scores = new ArrayList<>(dualFiniteParams.length);
		for (int i = 0; i < dualFiniteParams.length; i++) {
			scores.add(null);
			final Term param = dualFiniteParams[i];
			if (QuantifierUtils.isCorrespondingFiniteJunction(quantifier, param)) {
				scores.set(i, Double.valueOf(0));
				for (final TermVariable eliminatee : eliminatees) {
					final Result res = new XnfScout(script, quantifier, eliminatee, null).transduce(param);
					final double ratio = ratioProvider.apply(res);
					scores.set(i, scores.get(i) + ratio);
				}
			}
		}
		final float currentMax = 0;
		int argMax = -1;
		for (int i = 0; i < scores.size(); i++) {
			if (scores.get(i) != null && scores.get(i) > currentMax) {
				argMax = i;
			}
		}
		return argMax;
	}

	public static int computeRecommendationDer(final Script script, final Set<TermVariable> eliminatees,
			final Term[] dualFiniteParams, final int quantifier) {
		return computeRecommendation(script, eliminatees, dualFiniteParams, quantifier, x -> x.computeDerRatio());
	}

	public static int computeRecommendationEliminable(final Script script, final Set<TermVariable> eliminatees,
			final Term[] dualFiniteParams, final int quantifier) {
		return computeRecommendation(script, eliminatees, dualFiniteParams, quantifier,
				x -> x.computeEliminableRatio());
	}

	/**
	 * Alternative recommendation (see {@link XnfScout#computeRecommendation} where
	 * we first select the "best" eliminatee and utilize only this eliminatee to
	 * recommend a parameter.
	 */
	public static int computeRecommendation2(final Script script, final Set<TermVariable> eliminatees,
			final Term[] dualFiniteParams, final int quantifier) {
		final TermVariable bestEliminatee = selectBestEliminatee(script, quantifier, new ArrayList<>(eliminatees),
				Arrays.asList(dualFiniteParams));
		int res = computeRecommendationDer(script, Collections.singleton(bestEliminatee), dualFiniteParams, quantifier);
		if (res == -1) {
			res = computeRecommendationEliminable(script, Collections.singleton(bestEliminatee), dualFiniteParams,
					quantifier);
		}
		final int alt = computeRecommendation(script, eliminatees, dualFiniteParams, quantifier);
		if (res != alt) {
			bestEliminatee.toString();
		}
		return res;
	}

}
