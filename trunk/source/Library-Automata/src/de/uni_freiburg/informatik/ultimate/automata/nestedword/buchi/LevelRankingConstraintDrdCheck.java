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

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;

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

	public LevelRankingConstraintDrdCheck(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand,
			final boolean predecessorOwasEmpty, final int userDefinedMaxRank, final boolean useDoubleDeckers,
			final boolean predecessorLrsIsPowersetComponent, final LevelRankingState<LETTER, STATE> predecessorLrs) {
		super(operand, predecessorOwasEmpty, userDefinedMaxRank, useDoubleDeckers, predecessorLrsIsPowersetComponent,
				predecessorLrs);
	}

	public LevelRankingConstraintDrdCheck() {
		super();
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
	@Deprecated
	public boolean isTargetOfConfluenceForcedDelayedRankDecrease() {
		if (isNonAcceptingSink()) {
			return false;
		}
		for (final Entry<StateWithRankInfo<STATE>, HashMap<STATE, Integer>> entry : mLevelRanking.entrySet()) {
			// TODO Christian 2016-09-13: For clarity, this should not be a loop because it is executed at most once.
			for (final STATE upState : entry.getValue().keySet()) {
				final Set<Integer> predRanksOfNonAccepting =
						getRanksOfNonAcceptingPredecessors(entry.getKey(), upState);
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

	public boolean isTargetOfConfluenceForcedDelayedRankDecrease(final EnumSet<VoluntaryRankDecrease> voluntaryRankDecrease) {
		for (final StateWithRankInfo<STATE> down : mPredecessors.projectToFst()) {
			for (final STATE up : mPredecessors.projectToSnd(down)) {
				// Only applicable if current state has odd rank
				if (isOdd(getRank(down, up))) {
					final List<DoubleDecker<StateWithRankInfo<STATE>>> predecessorsEvenRank = new ArrayList<>();
					final List<DoubleDecker<StateWithRankInfo<STATE>>> predecessorsOddRank = new ArrayList<>();
					for (final DoubleDecker<StateWithRankInfo<STATE>> predecessor : mPredecessors.projectToTrd(down, up)) {
						if (isEven(predecessor.getUp().getRank())) {
							predecessorsEvenRank.add(predecessor);
						} else {
							assert isOdd(predecessor.getUp().getRank());
							predecessorsOddRank.add(predecessor);
						}
					}
					if (!predecessorsEvenRank.isEmpty() && !predecessorsOddRank.isEmpty()) {
						// current has odd rank and there are predecessors with even rank
						// hence all even rank were forced to decrease by confluence
						// now we only have to find out if this delayed rank decrease
						for (final DoubleDecker<StateWithRankInfo<STATE>> predecessor : predecessorsEvenRank) {
							if (voluntaryRankDecrease
									.equals(EnumSet.of(VoluntaryRankDecrease.ALL_EVEN_PREDECESSORS_ARE_ACCEPTING))) {
								if (!mOperand.isFinal(predecessor.getUp().getState())) {
									// some predecessor is not final, there is also a copy in which this was
									// decreased before
									return true;
								}
							} else if (voluntaryRankDecrease.equals(EnumSet.of(
									VoluntaryRankDecrease.ALLOWS_O_ESCAPE_AND_ALL_EVEN_PREDECESSORS_ARE_ACCEPTING,
									VoluntaryRankDecrease.PREDECESSOR_HAS_EMPTY_O))) {
								if (!mOperand.isFinal(predecessor.getUp().getState()) && predecessor.getUp().isInO()) {
									// some predecessor is not final but in O, there is also a copy in which this
									// was decreased before
									return true;
								}
							} else {
								throw new UnsupportedOperationException("unclear if CFDRD optimization is sound");
							}
						}
						return false;
					}

				}

			}
		}
		return false;
	}



	private Set<Integer> getRanksOfNonAcceptingPredecessors(final StateWithRankInfo<STATE> downState,
			final STATE upState) {
		final Set<Integer> result = new HashSet<>();
		for (final DoubleDecker<StateWithRankInfo<STATE>> pred : mPredecessors.projectToTrd(downState, upState)) {
			if (!mOperand.isFinal(pred.getUp().getState())) {
				result.add(pred.getUp().getRank());
			}
		}
		return result;
	}

	private Set<Integer> getEvenRanksOfNonAcceptingPredecessors(final StateWithRankInfo<STATE> downState,
			final STATE upState) {
		final Set<Integer> result = new HashSet<>();
		for (final DoubleDecker<StateWithRankInfo<STATE>> pred : mPredecessors.projectToTrd(downState, upState)) {
			if (isEven(pred.getUp().getRank())) {
				if (!mOperand.isFinal(pred.getUp().getState())) {
					result.add(pred.getUp().getRank());
				}
			}
		}
		return result;
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
		return getEvenRanksOfNonAcceptingPredecessors(downState, upState).isEmpty();
	}


//	public boolean nonAcceptingPredecessorsInOWithEvenRanksIsEmpty(final StateWithRankInfo<STATE> downState,
//			final STATE upState, final LevelRankingState<LETTER, STATE> predecessorLrs) {
//		for (final Triple<StateWithRankInfo<STATE>, STATE, Integer> dd : mRanksOfPredecessorsNonAcceptingPredecessorsEven) {
//			if (!predecessorLrs.inO(dd.getFirst(), dd.getSecond())) {
//				return false;
//			}
//		}
//		return true;
//	}

	@Deprecated
	private boolean isEligibleForVoluntaryRankDecrease(final StateWithRankInfo<STATE> downState, final STATE upState,
			final boolean allowDelayedRankDecrease) {
		final Integer constraint = getRank(downState, upState);
		if (allowDelayedRankDecrease) {
			return isEven(constraint) && !mOperand.isFinal(upState);
		}
		final Set<Integer> nonAcceptingEvenranks =
				getEvenRanksOfNonAcceptingPredecessors(downState, upState);
		return isEven(constraint) && !mOperand.isFinal(upState) && nonAcceptingEvenranks.isEmpty();
	}



//	@Override
//	public Set<DoubleDecker<StateWithRankInfo<STATE>>> getPredecessorWasAccepting() {
//		final Set<DoubleDecker<StateWithRankInfo<STATE>>> result = new HashSet<>();
//		for (final StateWithRankInfo<STATE> downState : getDownStates()) {
//			for (final StateWithRankInfo<STATE> upState : getUpStates(downState)) {
//				if (isEligibleForVoluntaryRankDecrease(downState, upState.getState(), true)) {
//					result.add(new DoubleDecker<>(downState, upState));
//				}
//			}
//		}
//		return result;
//	}


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


//	@Override
//	public boolean isEligibleForVoluntaryRankDecrease(final boolean voluntaryRankDecreaseOnlyIfSomePredecessorWasAccepting,
//			final boolean voluntaryRankDecreaseOnlyIfEnablesEscapeFromO, final boolean omitConfluenceEnforcedDelayedRankDecrease, final DoubleDecker<StateWithRankInfo<STATE>> dd) {
//		boolean result;
//		result = super.isEligibleForVoluntaryRankDecrease(voluntaryRankDecreaseOnlyIfSomePredecessorWasAccepting,
//				voluntaryRankDecreaseOnlyIfSomePredecessorWasAccepting, false, dd);
////		result &= (!omitConfluenceEnforcedDelayedRankDecrease)
//		return result;
//	}

}
