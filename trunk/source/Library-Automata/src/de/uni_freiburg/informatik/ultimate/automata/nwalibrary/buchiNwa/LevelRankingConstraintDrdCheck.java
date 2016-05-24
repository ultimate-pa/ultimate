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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.util.relation.HashRelation3;

/**
 * LevelRankingConstraintWithDelayedRankDecreaseCheck
 * @author Matthias Heizmann
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class LevelRankingConstraintDrdCheck<LETTER, STATE> extends LevelRankingConstraint<LETTER, STATE> {
	
	
	private final HashRelation3<StateWithRankInfo<STATE>, STATE, Integer> mRanksOfPredecessorsNonAcceptingPredecessors;
	private final HashRelation3<StateWithRankInfo<STATE>, STATE, Integer> mRanksOfPredecessorsNonAcceptingPredecessorsEven;

	public LevelRankingConstraintDrdCheck(INestedWordAutomatonSimple<LETTER, STATE> operand,
			boolean predecessorOwasEmpty,
			int userDefinedMaxRank, boolean useDoubleDeckers) {
		super(operand, predecessorOwasEmpty, userDefinedMaxRank, useDoubleDeckers);
		mRanksOfPredecessorsNonAcceptingPredecessors = new HashRelation3<>();
		mRanksOfPredecessorsNonAcceptingPredecessorsEven = new HashRelation3<>();
	}
	
	/**
	 * {@inheritDoc}
	 */
	public LevelRankingConstraintDrdCheck() {
		super();
		mRanksOfPredecessorsNonAcceptingPredecessors = null;
		mRanksOfPredecessorsNonAcceptingPredecessorsEven = null;
	}

	@Override
	protected void addConstaint(StateWithRankInfo<STATE> down, STATE up, Integer predecessorRank, boolean predecessorIsInO,
			boolean predecessorIsAccepting) {
		if (!predecessorIsAccepting) {
			mRanksOfPredecessorsNonAcceptingPredecessors.addTriple(down, up, predecessorRank);
			if (isEven(predecessorRank)) {
				mRanksOfPredecessorsNonAcceptingPredecessorsEven.addTriple(down, up, predecessorRank);
			}
		}
		super.addConstaint(down, up, predecessorRank, predecessorIsInO, predecessorIsAccepting);
	}
	
	
	/**
	 * We say that a transition stems from a delayed rank decrease if there
	 * is a state which has even and odd predecessors. Here, we neglect the
	 * highest odd if it is higher than the highest even rank.
	 * Rationale: Odd ranks occur only in the beginning or as result of a
	 * voluntary rank decrease (if after a final state the rank was decreased).
	 * This means that for each of these (delayed rank decrease) transitions
	 * there is also a transition whose source is the level ranking in which
	 * the rank was not voluntarily decreased.
	 * This interferes with other optimizations (e.g., tight level rankings, 
	 * elastic level rankings) because there the not voluntarily decreased
	 * path was lost is some state in between was not tight (resp. elastic) 
	 */
	public boolean isTargetOfDelayedRankDecrease() {
		if (isNonAcceptingSink()) {
			return false;
		}
		for (Entry<StateWithRankInfo<STATE>, HashMap<STATE, Integer>> entry : mLevelRanking.entrySet()) {
			for (STATE up : entry.getValue().keySet()) {
				Set<Integer> predRanksOfNonAccepting = mRanksOfPredecessorsNonAcceptingPredecessors.projectToTrd(entry.getKey(), up);
				if (predRanksOfNonAccepting.size() <= 1) {
					return false;
				} else {
					TreeSet<Integer> even = new TreeSet<>();
					TreeSet<Integer> odd = new TreeSet<>();
					for (Integer i : predRanksOfNonAccepting) {
						if (isEven(i)) {
							even.add(i);
						} else {
							assert isOdd(i);
							odd.add(i);
						}
					}
					if (odd.isEmpty() || even.isEmpty()) {
						return false;
					} else {
						Integer largestOdd = odd.last();
						Integer largestEven = even.last();
						if (largestOdd > largestEven) {
							odd.remove(largestOdd);
						}
						return !odd.isEmpty() && !even.isEmpty();
					}
				}
			}
		}
		return false;
	}
	
	public boolean nonAcceptingPredecessorsWithEvenRanksIsEmpty(StateWithRankInfo<STATE> down, STATE up) {
		return mRanksOfPredecessorsNonAcceptingPredecessorsEven.projectToTrd(down, up).isEmpty();
	}
	
	private boolean isEligibleForVoluntaryRankDecrease(StateWithRankInfo<STATE> down, STATE up, boolean allowDelayedRankDecrease) {
		Integer constraint = getRank(down, up);
		if (allowDelayedRankDecrease) {
			return (isEven(constraint) && !mOperand.isFinal(up));
		} else {
			Set<Integer> nonAcceptingEvenranks = mRanksOfPredecessorsNonAcceptingPredecessorsEven.projectToTrd(down, up);
			return (isEven(constraint) && !mOperand.isFinal(up) && nonAcceptingEvenranks.isEmpty());
		}
	}

	@Override
	public Set<DoubleDecker<StateWithRankInfo<STATE>>> getPredecessorWasAccepting() {
		Set<DoubleDecker<StateWithRankInfo<STATE>>> result = new HashSet<>();
		for (StateWithRankInfo<STATE> down : getDownStates()) {
			for (StateWithRankInfo<STATE> up : getUpStates(down)) {
				if (isEligibleForVoluntaryRankDecrease(down, up.getState(), true)) {
					result.add(new DoubleDecker<StateWithRankInfo<STATE>>(down, up));
				}
			}
		}
		return result;
	}
	
	

}
