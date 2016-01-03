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
	
	
	private final HashRelation3<StateWithRankInfo<STATE>, STATE, Integer> m_RanksOfNonFinalPredecessors_Even;
	private final HashRelation3<StateWithRankInfo<STATE>, STATE, Integer> m_RanksOfNonFinalPredecessors_Odd;
	private final HashRelation3<StateWithRankInfo<STATE>, STATE, Integer> m_RanksOfFinalPredecessors;

	public LevelRankingConstraintDrdCheck(INestedWordAutomatonSimple<LETTER, STATE> operand,
			boolean predecessorOwasEmpty,
			int userDefinedMaxRank, boolean useDoubleDeckers) {
		super(operand, predecessorOwasEmpty, userDefinedMaxRank, useDoubleDeckers);
		m_RanksOfNonFinalPredecessors_Even = new HashRelation3<>();
		m_RanksOfNonFinalPredecessors_Odd = new HashRelation3<>();
		m_RanksOfFinalPredecessors = new HashRelation3<>();
	}
	
	/**
	 * {@inheritDoc}
	 */
	public LevelRankingConstraintDrdCheck() {
		super();
		m_RanksOfNonFinalPredecessors_Even = null;
		m_RanksOfNonFinalPredecessors_Odd = null;
		m_RanksOfFinalPredecessors = null;
	}

	@Override
	protected void addConstaint(StateWithRankInfo<STATE> down, STATE up, Integer predecessorRank, boolean predecessorIsInO,
			boolean predecessorIsAccepting) {
		if (isEven(predecessorRank) && !predecessorIsAccepting) {
			m_RanksOfNonFinalPredecessors_Even.addTriple(down, up, predecessorRank);
		}
		super.addConstaint(down, up, predecessorRank, predecessorIsInO, predecessorIsAccepting);
	}
	
	
	public boolean isTargetOfDelayedRankDecrease(Integer maxRank) {
		for (Entry<StateWithRankInfo<STATE>, HashMap<STATE, Integer>> entry : m_LevelRanking.entrySet()) {
			for (STATE up : entry.getValue().keySet()) {
				if (m_Operand.isFinal(up)) {
					// do nothing
					// if operand is final we tolerate any rank decrease
					// this can probably be improved
					// e.g., if we have ranks 6 and 5 we know (tight 
					// level rankings) that some time ago 5 was 6 hence there
					// should be also a run where the state with 5 has an even rank
				} else {
					Set<Integer> nonFinalEven = m_RanksOfNonFinalPredecessors_Even.projectToTrd(entry.getKey(), up);
					Set<Integer> nonFinalOdd = m_RanksOfNonFinalPredecessors_Odd.projectToTrd(entry.getKey(), up);
					if (nonFinalEven.isEmpty()) {
						// do nothing
					} else {
						// maybe we can additionally require that all even ranks are similar
						// e.g., if we have predecessors with 4 and 2, there is
						// also a run where 2 is still 4.
						// 2016-01-02 Matthias: No we cannot, see simple rnk5 example
						if (nonFinalOdd.isEmpty()) {
							// do nothing
						} else {
							if (nonFinalOdd.size() == 1 && nonFinalOdd.contains(maxRank)) {
								// do nothing
								// 
							} else {
								return true;
							}
						}
					}
				}
			}
		}
		return false;
	}
	
	@Deprecated
	public boolean aroseFromDelayedRankDecrease() {
		for (StateWithRankInfo<STATE> down : m_RanksOfNonFinalPredecessors_Even.projectToFst()) {
			for (STATE up : m_RanksOfNonFinalPredecessors_Even.projectToSnd(down)) {
				Integer constraint = getRank(down, up);
				Set<Integer> nonAcceptingEvenranks = m_RanksOfNonFinalPredecessors_Even.projectToTrd(down, up);
				if (isOdd(constraint) && !nonAcceptingEvenranks.isEmpty()) {
					return true;
				}
			}
		}
		return false;
	}
	
	private boolean isEligibleForVoluntaryRankDecrease(StateWithRankInfo<STATE> down, STATE up) {
		Integer constraint = getRank(down, up);
		Set<Integer> nonAcceptingEvenranks = m_RanksOfNonFinalPredecessors_Even.projectToTrd(down, up);
		return (isEven(constraint) && !m_Operand.isFinal(up) && nonAcceptingEvenranks.isEmpty());
	}

	@Override
	@Deprecated
	public Set<DoubleDecker<StateWithRankInfo<STATE>>> getPredecessorWasAccepting() {
		Set<DoubleDecker<StateWithRankInfo<STATE>>> result = new HashSet<>();
		for (StateWithRankInfo<STATE> down : getDownStates()) {
			for (StateWithRankInfo<STATE> up : getUpStates(down)) {
				if (isEligibleForVoluntaryRankDecrease(down, up.getState())) {
					result.add(new DoubleDecker<StateWithRankInfo<STATE>>(down, up));
				}
			}
		}
		return result;
	}
	
	

}
