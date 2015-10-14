/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IDeterminizedState;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;

/**
 * Constraints that define a set of LevelRankingStates.
 * <ul>
 * <li> m_LevelRanking represents an upper bound for ranks of 
 * LevelRankingStates defined by this LevelRankingConstraints.
 * <li> A DoubleDecker is in LevelRankingState.m_O iff (it is in 
 *   LevelRankingConstraints.m_O and it has an even level rank)
 * </ul>
 */
public class LevelRankingConstraint<LETTER, STATE> extends LevelRankingState<LETTER, STATE> {
	private final int m_UserDefinedMaxRank;
	/**
	 * if !m_UseDoubleDeckers we always use getEmptyStackState()
	 * as down state to obtain sets of states instead of
	 * sets of DoubleDeckers.
	 */
	private final boolean m_UseDoubleDeckers;
	
	/**
	 * Information if the direct predecessor of a DoubleDecker was accepting.
	 * If this information is used by the LevelRankingGenerator.
	 */
	private final Set<DoubleDecker<StateWithRankInfo<STATE>>> m_PredecessorWasAccepting = 
			new HashSet<DoubleDecker<StateWithRankInfo<STATE>>>();
	
	public LevelRankingConstraint(
			INestedWordAutomatonSimple<LETTER, STATE> operand,
			int userDefinedMaxRank,
			boolean useDoubleDeckers) {
		super(operand);
		m_UserDefinedMaxRank = userDefinedMaxRank;
		m_UseDoubleDeckers = useDoubleDeckers;
	}
	
	/**
	 * Constructor for the constraint that is only satisfied by the
	 * non accepting sink state.
	 */
	public LevelRankingConstraint() {
		super();
		m_UserDefinedMaxRank = -1;
		m_UseDoubleDeckers = true;
	}

	void internalSuccessorConstraints(IFkvState<LETTER, STATE> state, LETTER symbol) {
		for (StateWithRankInfo<STATE> down : state.getDownStates()) {
			for (StateWithRankInfo<STATE> up : state.getUpStates(down)) {
				boolean oCandidate;
				Integer upRank;
				if (state instanceof LevelRankingState) {
					LevelRankingState<LETTER, STATE> lvlRkState = (LevelRankingState<LETTER, STATE>) state;
					oCandidate = lvlRkState.isOempty() || up.isInO();
					upRank = up.getRank();
				} else {
					assert (state instanceof FkvSubsetComponentState);
					// we use true, the predecessor was a deterministic
					// state. we treat this like "O is empty".
					// (this will safe some states)
					oCandidate = true;
					upRank = m_UserDefinedMaxRank;
				}
				for (OutgoingInternalTransition<LETTER, STATE> trans : 
								m_Operand.internalSuccessors(up.getState(),symbol)) {
					addConstaint(down, trans.getSucc(), upRank, oCandidate, m_Operand.isFinal(up.getState()));
				}
			}
		}
	}
	
	void callSuccessorConstraints(IFkvState<LETTER, STATE> state, LETTER symbol) {
		for (StateWithRankInfo<STATE> down : state.getDownStates()) {
			for (StateWithRankInfo<STATE> up : state.getUpStates(down)) {
				boolean oCandidate;
				Integer upRank;
				if (state instanceof LevelRankingState) {
					LevelRankingState<LETTER, STATE> lvlRkState = (LevelRankingState<LETTER, STATE>) state;
					oCandidate = lvlRkState.isOempty() || up.isInO();
					upRank = up.getRank();
				} else {
					assert (state instanceof FkvSubsetComponentState);
					// we use true, the predecessor was a deterministic
					// state. we treat this like "O is empty".
					// (this will safe some states)
					oCandidate = true;
					upRank = m_UserDefinedMaxRank;
				}
				for (OutgoingCallTransition<LETTER, STATE> trans : 
								m_Operand.callSuccessors(up.getState(),symbol)) {
					StateWithRankInfo<STATE> succDownState;
					// if !m_UseDoubleDeckers we always use getEmptyStackState()
					// as down state to obtain sets of states instead of
					// sets of DoubleDeckers.
					if (m_UseDoubleDeckers) {
						succDownState = up;
					} else {
						succDownState = new StateWithRankInfo<STATE>(m_Operand.getEmptyStackState());
					}
					addConstaint(succDownState, trans.getSucc(), upRank, oCandidate, m_Operand.isFinal(up.getState()));
				}
			}
		}
	}
	
	void returnSuccessorConstraints(IFkvState<LETTER, STATE> state, 
			IFkvState<LETTER, STATE> hier, LETTER symbol) {
		for (StateWithRankInfo<STATE> hierDown : hier.getDownStates()) {
			for (StateWithRankInfo<STATE> hierUp : hier.getUpStates(hierDown)) {
				if (state.getDownStates().isEmpty()) {
					continue;
					//throw new AssertionError();
				}
				StateWithRankInfo<STATE> downState;
				if (m_UseDoubleDeckers) {
					if (!state.getDownStates().contains(hierUp)) {
						continue;
					}
					downState = hierUp;
				} else {
					assert state.getDownStates().size() == 1;
					assert state.getDownStates().iterator().next() == 
											m_Operand.getEmptyStackState();
					// if !m_UseDoubleDeckers we always use getEmptyStackState()
					// as down state to obtain sets of states instead of
					// sets of DoubleDeckers.
					downState = new StateWithRankInfo<STATE>(m_Operand.getEmptyStackState());

				}
				Iterable<StateWithRankInfo<STATE>> upStates = state.getUpStates(downState);
				addReturnSuccessorConstraintsGivenDownState(state,
						downState, upStates, hierDown, hierUp, symbol);
			}
		}
	}

	private void addReturnSuccessorConstraintsGivenDownState(
			IFkvState<LETTER, STATE> state, StateWithRankInfo<STATE> downState, 
			Iterable<StateWithRankInfo<STATE>> upStates,
			StateWithRankInfo<STATE> hierDown, StateWithRankInfo<STATE> hierUp, 
			LETTER symbol) {
		for (StateWithRankInfo<STATE> stateUp : upStates) {
			boolean oCandidate;
			Integer upRank;
			if (state instanceof LevelRankingState) {
				//TODO: obtain rank and inO directly from StateWithRankInfo
				LevelRankingState<LETTER, STATE> lvlRkState = (LevelRankingState<LETTER, STATE>) state;
				oCandidate = lvlRkState.isOempty() || lvlRkState.inO(downState,stateUp.getState());
				upRank = lvlRkState.getRank(downState, stateUp.getState());
			} else {
				assert (state instanceof FkvSubsetComponentState);
				// we use true, the predecessor was a deterministic
				// state. we treat this like "O is empty".
				// (this will safe some states)
				oCandidate = true;
				upRank = m_UserDefinedMaxRank;
			}
			for (OutgoingReturnTransition<LETTER, STATE> trans : 
							m_Operand.returnSucccessors(stateUp.getState(),hierUp.getState(),symbol)) {
				assert m_UseDoubleDeckers || hierDown == m_Operand.getEmptyStackState();
				addConstaint(hierDown, trans.getSucc(), upRank, oCandidate, m_Operand.isFinal(stateUp.getState()));
			}
		}
	}

	

	
	/**
	 * Add constraint to the double decker (down,up). This constraints
	 * are only obtained from incoming transitions. Further constraints
	 * (odd rank only allowed for non-finals or state in o if not odd)
	 * are added later.
	 */
	protected void addConstaint(StateWithRankInfo<STATE> down, STATE up, 
			Integer rank, boolean oCandidate, boolean predecessorWasAccepting) {
		// This method is very similar to addRank(), but it does not 
		// override a rank that was already set (instead takes the minimum) 
		// and one assert is missing.
		assert rank != null;
		HashMap<STATE, Integer> up2rank = m_LevelRanking.get(down);
		if (up2rank == null) {
			up2rank = new HashMap<STATE,Integer>();
			m_LevelRanking.put(down, up2rank);
		}
		Integer oldRank = up2rank.get(up);
		if (oldRank == null || oldRank > rank) {
			up2rank.put(up,rank);
		}
		if (oCandidate) {
			addToO(down,up);
		}
		if (m_HighestRank < rank) {
			m_HighestRank = rank;
		}
		if (predecessorWasAccepting) {
			m_PredecessorWasAccepting.add(new DoubleDecker<StateWithRankInfo<STATE>>(
					down, new StateWithRankInfo<STATE>(up, rank, oCandidate)));
		}
	}


	public Set<DoubleDecker<StateWithRankInfo<STATE>>> getPredecessorWasAccepting() {
		return m_PredecessorWasAccepting;
	}		
}
