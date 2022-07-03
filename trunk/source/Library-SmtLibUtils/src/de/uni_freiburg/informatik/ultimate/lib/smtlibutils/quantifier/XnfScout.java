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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier;

import java.util.Arrays;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryEqualityRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class XnfScout extends CondisTermTransducer<XnfScout.Result> {

	public enum Adk {
		ATOM, DISJUNCTION, CONJUNCTION
	}

	public enum Occurrence {
		DER, ELIMINATABLE, OTHER_OCCURRENCE, ABSENT
	};

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
				// For simplicity we assume that the array variable is always eliminatable. This
				// is however not true if the array is, e.g., the parameter of a function symbol
				// or the index of another array.
				return Occurrence.ELIMINATABLE;
			}
		} else {
			final PolynomialRelation polyRel = PolynomialRelation.convert(script, term);
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
				return Occurrence.ELIMINATABLE;
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
		final long eliminatableCorrespondingJuncts;
		final long occurringCorrespondingJuncts;
		final boolean atLeastOneNonInvolvedCorrespondingJunct;
		final Occurrence classification = classify(mScript, mQuantifier, term, mEliminatee, mQuantifiedInAncestors);
		switch (classification) {
		case ABSENT:
			derCorrespondingJuncts = 0;
			eliminatableCorrespondingJuncts = 0;
			occurringCorrespondingJuncts = 0;
			atLeastOneNonInvolvedCorrespondingJunct = true;
			break;
		case DER:
			derCorrespondingJuncts = 1;
			eliminatableCorrespondingJuncts = 0;
			occurringCorrespondingJuncts = 0;
			atLeastOneNonInvolvedCorrespondingJunct = false;
			break;
		case ELIMINATABLE:
			derCorrespondingJuncts = 0;
			eliminatableCorrespondingJuncts = 1;
			occurringCorrespondingJuncts = 0;
			atLeastOneNonInvolvedCorrespondingJunct = false;
			break;
		case OTHER_OCCURRENCE:
			derCorrespondingJuncts = 0;
			eliminatableCorrespondingJuncts = 0;
			occurringCorrespondingJuncts = 1;
			atLeastOneNonInvolvedCorrespondingJunct = false;
			break;
		default:
			throw new AssertionError("unknown value: " + classification);
		}
		return new Result(Adk.ATOM, derCorrespondingJuncts, eliminatableCorrespondingJuncts,
				occurringCorrespondingJuncts, atLeastOneNonInvolvedCorrespondingJunct);
	}

	@Override
	protected Result transduceConjunction(final List<Result> transducedArguments) {
		final Result result;
		if (mQuantifier == QuantifiedFormula.EXISTS) {
			result = transduceDual(Adk.CONJUNCTION, transducedArguments);
		} else if (mQuantifier == QuantifiedFormula.FORALL) {
			result = transduceCorresponding(Adk.CONJUNCTION, transducedArguments);
		} else {
			throw new AssertionError("Unknown quantifier " + mQuantifier);
		}
		return result;
	}

	private Result transduceCorresponding(final Adk adk, final List<Result> transducedArguments) {
		long derCorrespondingJuncts = 0;
		long eliminatableCorrespondingJuncts = 0;
		long occurringCorrespondingJuncts = 0;
		boolean atLeastOneNonInvolvedCorrespondingJunct = false;
		for (final Result arg : transducedArguments) {
			if (arg.getAdk() == adk) {
				throw new AssertionError("Expected alternation between conjunction and disjunction");
			}
			derCorrespondingJuncts += arg.getDerCorrespondingJuncts();
			eliminatableCorrespondingJuncts += arg.getEliminatableCorrespondingJuncts();
			occurringCorrespondingJuncts += arg.getOccurringCorrespondingJuncts();
			atLeastOneNonInvolvedCorrespondingJunct |= arg.isAtLeastOneNonInvolvedCorrespondingJunct();
		}
		return new Result(adk, derCorrespondingJuncts, eliminatableCorrespondingJuncts, occurringCorrespondingJuncts,
				atLeastOneNonInvolvedCorrespondingJunct);
	}

	private Result transduceDual(final Adk adk, final List<Result> transducedArguments) {
		long derCorrespondingJuncts = transducedArguments.get(0).getDerCorrespondingJuncts();
		long eliminatableCorrespondingJuncts = transducedArguments.get(0).getEliminatableCorrespondingJuncts();
		long occurringCorrespondingJuncts = transducedArguments.get(0).getOccurringCorrespondingJuncts();
		boolean atLeastOneNonInvolvedCorrespondingJunct = transducedArguments.get(0)
				.isAtLeastOneNonInvolvedCorrespondingJunct();
		for (int i = 1; i < transducedArguments.size(); i++) {
			if (transducedArguments.get(i).getAdk() == adk) {
				throw new AssertionError("Expected alternation between conjunction and disjunction");
			}
			final long oldDerCorrespondingJuncts = derCorrespondingJuncts;
			final long oldEliminatableCorrespondingJuncts = eliminatableCorrespondingJuncts;
			final long oldEccurringCorrespondingJuncts = occurringCorrespondingJuncts;
			final long oldNonInvolved = (atLeastOneNonInvolvedCorrespondingJunct ? 1 : 0);

			final long operandDerCorrespondingJuncts = transducedArguments.get(i).getDerCorrespondingJuncts();
			final long operandEliminatableCorrespondingJuncts = transducedArguments.get(i)
					.getEliminatableCorrespondingJuncts();
			final long operandOccurringCorrespondingJuncts = transducedArguments.get(i)
					.getOccurringCorrespondingJuncts();
			final long operandNonInvolved = (transducedArguments.get(i).isAtLeastOneNonInvolvedCorrespondingJunct() ? 1
					: 0);

			derCorrespondingJuncts = oldDerCorrespondingJuncts * operandDerCorrespondingJuncts
					+ oldDerCorrespondingJuncts * operandEliminatableCorrespondingJuncts
					+ oldDerCorrespondingJuncts * operandOccurringCorrespondingJuncts
					+ oldDerCorrespondingJuncts * operandNonInvolved
					+ oldEliminatableCorrespondingJuncts * operandDerCorrespondingJuncts
					+ oldEccurringCorrespondingJuncts * operandDerCorrespondingJuncts
					+ oldNonInvolved * operandDerCorrespondingJuncts;
			occurringCorrespondingJuncts = oldEccurringCorrespondingJuncts * operandEliminatableCorrespondingJuncts
					+ oldEccurringCorrespondingJuncts * operandOccurringCorrespondingJuncts
					+ oldEccurringCorrespondingJuncts * operandNonInvolved
					+ oldEliminatableCorrespondingJuncts * operandOccurringCorrespondingJuncts
					+ oldNonInvolved * operandOccurringCorrespondingJuncts;
			eliminatableCorrespondingJuncts = oldEliminatableCorrespondingJuncts
					* operandEliminatableCorrespondingJuncts + oldEliminatableCorrespondingJuncts * operandNonInvolved
					+ oldNonInvolved * operandEliminatableCorrespondingJuncts;
			atLeastOneNonInvolvedCorrespondingJunct &= transducedArguments.get(i)
					.isAtLeastOneNonInvolvedCorrespondingJunct();
		}
		return new Result(adk, derCorrespondingJuncts, eliminatableCorrespondingJuncts, occurringCorrespondingJuncts,
				atLeastOneNonInvolvedCorrespondingJunct);
	}

	@Override
	protected Result transduceDisjunction(final List<Result> transducedArguments) {
		final Result result;
		if (mQuantifier == QuantifiedFormula.EXISTS) {
			result = transduceCorresponding(Adk.DISJUNCTION, transducedArguments);
		} else if (mQuantifier == QuantifiedFormula.FORALL) {
			result = transduceDual(Adk.DISJUNCTION, transducedArguments);
		} else {
			throw new AssertionError("Unknown quantifier " + mQuantifier);
		}
		return result;

	}

	public static class Result implements Comparable<Result> {
		private final Adk mAdk;
		private final boolean mAtLeastOneNonInvolvedCorrespondingJunct;
		private final long mDerCorrespondingJuncts;
		private final long mEliminatableCorrespondingJuncts;
		private final long mOccurringCorrespondingJuncts;

		public Result(final Adk adk, final long derCorrespondingJuncts, final long eliminatableCorrespondingJuncts,
				final long occurringCorrespondingJuncts, final boolean atLeastOneNonInvolvedCorrespondingJunct) {
			super();
			mAdk = adk;
			mAtLeastOneNonInvolvedCorrespondingJunct = atLeastOneNonInvolvedCorrespondingJunct;
			mDerCorrespondingJuncts = derCorrespondingJuncts;
			mEliminatableCorrespondingJuncts = eliminatableCorrespondingJuncts;
			mOccurringCorrespondingJuncts = occurringCorrespondingJuncts;
		}

		public Adk getAdk() {
			return mAdk;
		}

		public boolean isAtLeastOneNonInvolvedCorrespondingJunct() {
			return mAtLeastOneNonInvolvedCorrespondingJunct;
		}

		public long getDerCorrespondingJuncts() {
			return mDerCorrespondingJuncts;
		}

		public long getEliminatableCorrespondingJuncts() {
			return mEliminatableCorrespondingJuncts;
		}

		public long getOccurringCorrespondingJuncts() {
			return mOccurringCorrespondingJuncts;
		}

		@Override
		public String toString() {
			return String.format("%s: %s DER, %s eliminateable, %s other occurring, %s non-involved", mAdk,
					mDerCorrespondingJuncts, mEliminatableCorrespondingJuncts, mOccurringCorrespondingJuncts,
					mAtLeastOneNonInvolvedCorrespondingJunct);
		}

		@Override
		public int compareTo(final Result other) {
			{
				final int step1 = Long.valueOf(getOccurringCorrespondingJuncts())
						.compareTo(Long.valueOf(other.getOccurringCorrespondingJuncts()));
				if (step1 != 0) {
					return step1;
				}
			}
			{
				final int step2 = Long.valueOf(getEliminatableCorrespondingJuncts())
						.compareTo(Long.valueOf(other.getEliminatableCorrespondingJuncts()));
				if (step2 != 0) {
					return step2;
				}
			}
			{
				final int step3 = Long.valueOf(getDerCorrespondingJuncts())
						.compareTo(Long.valueOf(other.getDerCorrespondingJuncts()));
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

	}
}
