/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.SummaryReturnTransition;


/**
 * Check if down states of an automaton are stored consistent. This is slow!
 * Use only for testing on small examples.
 * @author heizmann@informatik.uni-freiburg.de
 */
public class DownStateConsistencyCheck<LETTER, STATE> {
	
	IDoubleDeckerAutomaton<LETTER, STATE> m_Nwa;
	
	public DownStateConsistencyCheck(IDoubleDeckerAutomaton<LETTER, STATE> nwa) {
		m_Nwa = nwa;
	}
	
	public boolean consistentForAll() {
		boolean result = true;
		result &= consistentForInitials();
		for (STATE state : m_Nwa.getStates()) {
			result &= consistentForState(state);
		}
		return result;
	}
	
	private boolean consistentForInitials() {
		boolean result = true;
		for (STATE state : m_Nwa.getInitialStates()) {
			Set<STATE> downStates = m_Nwa.getDownStates(state);
			result &= downStates.contains(m_Nwa.getEmptyStackState());
		}
		assert result;
		return result;
	}

	private boolean consistentForState(STATE state) {
		boolean result = true;
		Set<STATE> downStates = m_Nwa.getDownStates(state);
		result &= getIsComparison(state, downStates);
		result &= checkIfDownStatesArePassedToSuccessors(state, downStates);


//		for (IncomingInternalTransition<LETTER, STATE> t : m_Nwa.internalPredecessors(state)) {
//			result &= internalOut(t.getPred(), t.getLetter(), state);
//			assert result;
//		}

//		for (IncomingCallTransition<LETTER, STATE> t : m_Nwa.callPredecessors(state)) {
//			result &= callOut(t.getPred(), t.getLetter(), state);
//			assert result;
//		}

//		for (IncomingReturnTransition<LETTER, STATE> t : m_Nwa.returnPredecessors(state)) {
//			result &= returnOut(t.getLinPred(), t.getHierPred(), t.getLetter(), state);
//			assert result;
//			result &= returnSummary(t.getLinPred(), t.getHierPred(), t.getLetter(), state);
//			assert result;
//		}

		return result;
	}
	
	private boolean checkIfDownStatesArePassedToSuccessors(STATE state,
			Set<STATE> downStates) {
		boolean result = true;
		for (OutgoingInternalTransition<LETTER, STATE> t : m_Nwa.internalSuccessors(state)) {
			Set<STATE> succDownStates = m_Nwa.getDownStates(t.getSucc());
			result &= succDownStates.containsAll(downStates);
			assert result;
		}
		for (OutgoingCallTransition<LETTER, STATE> t : m_Nwa.callSuccessors(state)) {
			Set<STATE> succDownStates = m_Nwa.getDownStates(t.getSucc());
			result &= succDownStates.contains(state);
			assert result;
		}
		for (OutgoingReturnTransition<LETTER, STATE> t : m_Nwa.returnSuccessors(state)) {
			Set<STATE> succDownStates = m_Nwa.getDownStates(t.getSucc());
			Set<STATE> hierDownStates = m_Nwa.getDownStates(t.getHierPred());
			if (downStates.contains(t.getHierPred())) {
				result &= succDownStates.containsAll(hierDownStates);
				assert result;
			} else {
				// nothing to check, we cannot take this transition
			}
		}
		for (SummaryReturnTransition<LETTER, STATE> t : m_Nwa.returnSummarySuccessor(state)) {
			Set<STATE> succDownStates = m_Nwa.getDownStates(t.getSucc());
			result &= succDownStates.containsAll(downStates);
			assert result;
		}
		return result;
	}

	/**
	 * Check if {@link IDoubleDeckerAutomaton#getDownStates(Object)} and 
	 * {@link IDoubleDeckerAutomaton#isDoubleDecker(Object, Object)} are
	 * consistent.
	 */
	private boolean getIsComparison(STATE state, Set<STATE> downStates) {
		return getIsComparison1(state, downStates) 
				&& getIsComparison2(state, downStates);
	}

	
	/**
	 * Check if doubleDeckers claimed by 
	 * {@link IDoubleDeckerAutomaton#isDoubleDecker(Object, Object)}
	 * are a superset of the doubleDeckers claimed by
	 * {@link IDoubleDeckerAutomaton#getDownStates(Object)}
	 */
	private boolean getIsComparison1(STATE state, Set<STATE> downStates) {
		boolean result = true;
		for (STATE down : downStates) {
			result &= m_Nwa.isDoubleDecker(state, down);
		}
		return result;
	}
	
	/**
	 * Check if doubleDeckers claimed by 
	 * {@link IDoubleDeckerAutomaton#getDownStates(Object)}
	 * are a superset of the doubleDeckers claimed by
	 * {@link IDoubleDeckerAutomaton#isDoubleDecker(Object, Object)}
	 * This check is expensive, because we have to iterate over all states.
	 * 
	 */
	private boolean getIsComparison2(STATE state, Set<STATE> downStates) {
		boolean result = true;
		for (STATE down : m_Nwa.getStates()) {
			if (m_Nwa.isDoubleDecker(state, down)) {
				result &= downStates.contains(down);
			}
		}
		return result;
	}

}
