package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.HashMap;
import java.util.Set;

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
	
	public LevelRankingConstraint(
			INestedWordAutomatonSimple<LETTER, STATE> operand,
			int userDefinedMaxRank,
			boolean useDoubleDeckers) {
		super(operand);
		m_UserDefinedMaxRank = userDefinedMaxRank;
		m_UseDoubleDeckers = useDoubleDeckers;
	}

	void internalSuccessorConstraints(IDeterminizedState<LETTER, STATE> state, LETTER symbol) {
		for (STATE down : state.getDownStates()) {
			for (STATE up : state.getUpStates(down)) {
				boolean oCandidate;
				Integer upRank;
				if (state instanceof LevelRankingState) {
					LevelRankingState<LETTER, STATE> lvlRkState = (LevelRankingState<LETTER, STATE>) state;
					oCandidate = lvlRkState.isOempty() || lvlRkState.inO(down,up);
					upRank = lvlRkState.getRank(down, up);
				} else {
					// we use true, the predecessor was a deterministic
					// state. we treat this like "O is empty".
					// (this will safe some states)
					oCandidate = true;
					upRank = m_UserDefinedMaxRank;
				}
				for (OutgoingInternalTransition<LETTER, STATE> trans : 
								m_Operand.internalSuccessors(up,symbol)) {
					addConstaint(down, trans.getSucc(), upRank, oCandidate);
				}
			}
		}
	}
	
	void callSuccessorConstraints(IDeterminizedState<LETTER, STATE> state, LETTER symbol) {
		for (STATE down : state.getDownStates()) {
			for (STATE up : state.getUpStates(down)) {
				boolean oCandidate;
				Integer upRank;
				if (state instanceof LevelRankingState) {
					LevelRankingState<LETTER, STATE> lvlRkState = (LevelRankingState<LETTER, STATE>) state;
					oCandidate = lvlRkState.isOempty() || lvlRkState.inO(down,up);
					upRank = lvlRkState.getRank(down, up);
				} else {
					// we use true, the predecessor was a deterministic
					// state. we treat this like "O is empty".
					// (this will safe some states)
					oCandidate = true;
					upRank = m_UserDefinedMaxRank;
				}
				for (OutgoingCallTransition<LETTER, STATE> trans : 
								m_Operand.callSuccessors(up,symbol)) {
					STATE succDownState;
					// if !m_UseDoubleDeckers we always use getEmptyStackState()
					// as down state to obtain sets of states instead of
					// sets of DoubleDeckers.
					if (m_UseDoubleDeckers) {
						succDownState = up;
					} else {
						succDownState = m_Operand.getEmptyStackState();
					}
					addConstaint(succDownState, trans.getSucc(), upRank, oCandidate);
				}
			}
		}
	}
	
	void returnSuccessorConstraints(IDeterminizedState<LETTER, STATE> state, 
			IDeterminizedState<LETTER, STATE> hier, LETTER symbol) {
		for (STATE hierDown : hier.getDownStates()) {
			for (STATE hierUp : hier.getUpStates(hierDown)) {
				if (state.getDownStates().isEmpty()) {
					continue;
					//throw new AssertionError();
				}
				STATE downState;
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
					downState = m_Operand.getEmptyStackState();

				}
				Set<STATE> upStates = state.getUpStates(downState);
				addReturnSuccessorConstraintsGivenDownState(state,
						downState, upStates, hierDown, hierUp, symbol);
			}
		}
	}

	private void addReturnSuccessorConstraintsGivenDownState(
			IDeterminizedState<LETTER, STATE> state, STATE downState, Set<STATE> upStates,
			STATE hierDown, STATE hierUp, LETTER symbol) {
		for (STATE stateUp : upStates) {
			boolean oCandidate;
			Integer upRank;
			if (state instanceof LevelRankingState) {
				LevelRankingState<LETTER, STATE> lvlRkState = (LevelRankingState<LETTER, STATE>) state;
				oCandidate = lvlRkState.isOempty() || lvlRkState.inO(downState,stateUp);
				upRank = lvlRkState.getRank(downState, stateUp);
			} else {
				// we use true, the predecessor was a deterministic
				// state. we treat this like "O is empty".
				// (this will safe some states)
				oCandidate = true;
				upRank = m_UserDefinedMaxRank;
			}
			for (OutgoingReturnTransition<LETTER, STATE> trans : 
							m_Operand.returnSucccessors(stateUp,hierUp,symbol)) {
				assert m_UseDoubleDeckers || hierDown == m_Operand.getEmptyStackState();
				addConstaint(hierDown, trans.getSucc(), upRank, oCandidate);
			}
		}
	}

	

	
	/**
	 * Add constraint to the double decker (down,up). This constraints
	 * are only obtained from incoming transitions. Further constraints
	 * (odd rank only allowed for non-finals or state in o if not odd)
	 * are added later.
	 */
	protected void addConstaint(STATE down, STATE up, 
										Integer rank, boolean oCandidate) {
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
	}		
}