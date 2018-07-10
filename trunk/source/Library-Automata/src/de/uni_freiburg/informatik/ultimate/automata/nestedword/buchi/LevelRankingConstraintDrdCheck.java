/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * LevelRankingConstraintWithDelayedRankDecreaseCheck.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class LevelRankingConstraintDrdCheck<LETTER, STATE> extends LevelRankingConstraint<LETTER, STATE> {
	private final HashRelation3<StateWithRankInfo<STATE>, STATE, Integer> mRanksOfPredecessorsNonAcceptingPredecessors;
	private final HashRelation3<StateWithRankInfo<STATE>, STATE, Integer> mRanksOfPredecessorsNonAcceptingPredecessorsEven;

	public LevelRankingConstraintDrdCheck(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand,
			final boolean predecessorOwasEmpty, final int userDefinedMaxRank, final boolean useDoubleDeckers) {
		super(operand, predecessorOwasEmpty, userDefinedMaxRank, useDoubleDeckers);
		mRanksOfPredecessorsNonAcceptingPredecessors = new HashRelation3<>();
		mRanksOfPredecessorsNonAcceptingPredecessorsEven = new HashRelation3<>();
	}

	public LevelRankingConstraintDrdCheck() {
		super();
		mRanksOfPredecessorsNonAcceptingPredecessors = null;
		mRanksOfPredecessorsNonAcceptingPredecessorsEven = null;
	}

	@Override
	protected void addConstraint(final StateWithRankInfo<STATE> downState, final STATE upState,
			final Integer predecessorRank, final boolean predecessorIsInO, final boolean predecessorIsAccepting) {
		if (!predecessorIsAccepting) {
			mRanksOfPredecessorsNonAcceptingPredecessors.addTriple(downState, upState, predecessorRank);
			if (isEven(predecessorRank)) {
				mRanksOfPredecessorsNonAcceptingPredecessorsEven.addTriple(downState, upState, predecessorRank);
			}
		}
		super.addConstraint(downState, upState, predecessorRank, predecessorIsInO, predecessorIsAccepting);
	}

	/**
	 * We say that a transition stems from a confluence-forced delayed rank decrease
	 * if there is a state which has even and odd predecessors. Here, we neglect the
	 * highest odd if it is higher than the highest even rank. Rationale: Odd ranks
	 * occur only in the beginning or as result of a voluntary rank decrease (if
	 * after a final state the rank was decreased). This means that for each of
	 * these (delayed rank decrease) transitions there is also a transition whose
	 * source is the level ranking in which the rank was not voluntarily decreased.
	 * <br />
	 * This interferes with most other optimizations (e.g., tight level rankings,
	 * elastic level rankings, delayed rank decreases) because there the not
	 * voluntarily decreased path was lost if some state in between was not tight
	 * (resp. not elastic). <br />
	 * This is not tested very well for other complementations than the NCSB
	 * complementations.
	 *
	 */
	public boolean isTargetOfConfluenceForcedDelayedRankDecrease() {
		if (isNonAcceptingSink()) {
			return false;
		}
		for (final Entry<StateWithRankInfo<STATE>, HashMap<STATE, Integer>> entry : mLevelRanking.entrySet()) {
			// TODO Christian 2016-09-13: For clarity, this should not be a loop because it is executed at most once.
			for (final STATE upState : entry.getValue().keySet()) {
				final Set<Integer> predRanksOfNonAccepting =
						mRanksOfPredecessorsNonAcceptingPredecessors.projectToTrd(entry.getKey(), upState);
				if (predRanksOfNonAccepting.size() <= 1) {
					return false;
				}
				final TreeSet<Integer> even = new TreeSet<>();
				final TreeSet<Integer> odd = new TreeSet<>();
				sortRanks(predRanksOfNonAccepting, even, odd);
				if (odd.isEmpty() || even.isEmpty()) {
					return false;
				}
				final Integer largestOdd = odd.last();
				final Integer largestEven = even.last();
				if (largestOdd > largestEven) {
					odd.remove(largestOdd);
				}
				return !odd.isEmpty() && !even.isEmpty();
			}
		}
		return false;
	}


	/**
	 * @param downState
	 *            The down state.
	 * @param upState
	 *            up state
	 * @return {@code true} iff there is no non-accepting predecessor with even rank
	 */
	public boolean nonAcceptingPredecessorsWithEvenRanksIsEmpty(final StateWithRankInfo<STATE> downState,
			final STATE upState) {
		return mRanksOfPredecessorsNonAcceptingPredecessorsEven.projectToTrd(downState, upState).isEmpty();
	}


	public boolean nonAcceptingPredecessorsInOWithEvenRanksIsEmpty(final StateWithRankInfo<STATE> downState,
			final STATE upState, final LevelRankingState<LETTER, STATE> predecessorLrs) {
		for (final Triple<StateWithRankInfo<STATE>, STATE, Integer> dd : mRanksOfPredecessorsNonAcceptingPredecessorsEven) {
			if (!predecessorLrs.inO(dd.getFirst(), dd.getSecond())) {
				return false;
			}
		}
		return true;
	}


	private boolean isEligibleForVoluntaryRankDecrease(final StateWithRankInfo<STATE> downState, final STATE upState,
			final boolean allowDelayedRankDecrease) {
		final Integer constraint = getRank(downState, upState);
		if (allowDelayedRankDecrease) {
			return isEven(constraint) && !mOperand.isFinal(upState);
		}
		final Set<Integer> nonAcceptingEvenranks =
				mRanksOfPredecessorsNonAcceptingPredecessorsEven.projectToTrd(downState, upState);
		return isEven(constraint) && !mOperand.isFinal(upState) && nonAcceptingEvenranks.isEmpty();
	}

	@Override
	public Set<DoubleDecker<StateWithRankInfo<STATE>>> getPredecessorWasAccepting() {
		final Set<DoubleDecker<StateWithRankInfo<STATE>>> result = new HashSet<>();
		for (final StateWithRankInfo<STATE> downState : getDownStates()) {
			for (final StateWithRankInfo<STATE> upState : getUpStates(downState)) {
				if (isEligibleForVoluntaryRankDecrease(downState, upState.getState(), true)) {
					result.add(new DoubleDecker<>(downState, upState));
				}
			}
		}
		return result;
	}

	private static void sortRanks(final Set<Integer> predRanksOfNonAccepting, final TreeSet<Integer> even,
			final TreeSet<Integer> odd) {
		for (final Integer i : predRanksOfNonAccepting) {
			if (isEven(i)) {
				even.add(i);
			} else {
				assert isOdd(i);
				odd.add(i);
			}
		}
	}


	@Override
	public boolean isEligibleForVoluntaryRankDecrease(final boolean voluntaryRankDecreaseOnlyIfSomePredecessorWasAccepting,
			final boolean voluntaryRankDecreaseOnlyIfEnablesEscapeFromO, final boolean omitConfluenceEnforcedDelayedRankDecrease, final DoubleDecker<StateWithRankInfo<STATE>> dd) {
		boolean result;
		result = super.isEligibleForVoluntaryRankDecrease(voluntaryRankDecreaseOnlyIfSomePredecessorWasAccepting,
				voluntaryRankDecreaseOnlyIfSomePredecessorWasAccepting, false, dd);
//		result &= (!omitConfluenceEnforcedDelayedRankDecrease)
		return result;
	}

}
