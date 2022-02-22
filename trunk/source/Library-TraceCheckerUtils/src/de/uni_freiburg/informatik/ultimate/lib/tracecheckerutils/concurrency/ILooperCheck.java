/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.concurrency;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * Conservatively checks if a given letter is a universal looper. A looper has to be invariant under all predicates, and
 * it may never introduce a new predicate (i.e., have a postcondition which is not implied by the precondition).
 *
 * @param <L>
 *            The type of letters
 */
public interface ILooperCheck<L> {
	/**
	 * Checks if the given letter is a looper for the given set of predicates.
	 *
	 * @param letter
	 *            The letter to check
	 * @param states
	 *            The set of predicates to consider
	 * @param htc
	 * @param coverage
	 *
	 * @return true if the letter can be guaranteed to be a looper.
	 */
	boolean isUniversalLooper(final L letter, final Set<IPredicate> states);

	/**
	 * An efficient sound but (very) incomplete check for loopers: A letter is considered a looper, if it does not share
	 * any variables with any predicate.
	 *
	 * @param <L>
	 *            The type of letters
	 */
	public static class IndependentLooperCheck<L extends IAction> implements ILooperCheck<L> {
		@Override
		public boolean isUniversalLooper(final L letter, final Set<IPredicate> states) {
			if (letter.getTransformula().isInfeasible() != Infeasibility.UNPROVEABLE) {
				return false;
			}
			for (final IPredicate predicate : states) {
				final boolean isIndependent = isIndependent(letter, predicate);
				if (!isIndependent) {
					return false;
				}
			}
			return true;
		}

		private boolean isIndependent(final L letter, final IPredicate predicate) {
			final Set<IProgramVar> in = letter.getTransformula().getInVars().keySet();
			final Set<IProgramVar> out = letter.getTransformula().getOutVars().keySet();
			return !DataStructureUtils.haveNonEmptyIntersection(in, predicate.getVars())
					&& !DataStructureUtils.haveNonEmptyIntersection(out, predicate.getVars());
		}
	}

	/**
	 * A complete and sound looper check that uses an {@link IHoareTripleChecker}.
	 *
	 * @param <L>
	 *            The type of letters
	 */
	public static class HoareLooperCheck<L extends IAction> implements ILooperCheck<L> {
		private final IHoareTripleChecker mHtc;
		private final IPredicateCoverageChecker mCoverage;
		private final IndependentLooperCheck<L> mIndependentCheck = new IndependentLooperCheck<>();

		public HoareLooperCheck(final IHoareTripleChecker htc, final IPredicateCoverageChecker coverage) {
			mHtc = htc;
			mCoverage = coverage;
		}

		@Override
		public boolean isUniversalLooper(final L letter, final Set<IPredicate> states) {
			if (letter.getTransformula().isInfeasible() != Infeasibility.UNPROVEABLE) {
				return false;
			}
			if (mIndependentCheck.isUniversalLooper(letter, states)) {
				return true;
			}

			for (final IPredicate predicate : states) {
				final boolean isInvariant =
						mHtc.checkInternal(predicate, (IInternalAction) letter, predicate) == Validity.VALID;
				if (!isInvariant) {
					return false;
				}

				for (final IPredicate post : states) {
					if (mCoverage.isCovered(predicate, post) == Validity.VALID) {
						continue;
					}
					final boolean mayIntroduce =
							mHtc.checkInternal(predicate, (IInternalAction) letter, post) != Validity.INVALID;
					if (mayIntroduce) {
						return false;
					}
				}
			}
			return true;
		}
	}
}
