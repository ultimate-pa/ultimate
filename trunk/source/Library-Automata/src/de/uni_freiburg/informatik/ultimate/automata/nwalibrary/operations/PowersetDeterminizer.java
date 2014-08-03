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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DeterminizedState;


/**
 * Construct deterministic states like in the classical powerset construction.
 * For determinization of NWAs there is also a powerset construction. This
 * class implements the computation of deterministic successor states according
 * to this powerset construction.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER> Symbol
 * @param <STATE> Content
 */
public class PowersetDeterminizer<LETTER,STATE> 
			implements IStateDeterminizer<LETTER,STATE> {

	StateFactory<STATE> m_StateFactory;
	INestedWordAutomatonSimple<LETTER,STATE> m_Nwa;
	private final boolean m_UseDoubleDeckers;
	int maxDegreeOfNondeterminism = 0;
	
	public PowersetDeterminizer(INestedWordAutomatonSimple<LETTER,STATE> nwa, 
			boolean useDoubleDeckers, StateFactory<STATE> stateFactory) { 
		m_Nwa = nwa;
		m_UseDoubleDeckers = useDoubleDeckers;
		this.m_StateFactory = stateFactory;
	}

	
	@Override
	public DeterminizedState<LETTER,STATE> initialState() {
		DeterminizedState<LETTER,STATE> detState = 
			new DeterminizedState<LETTER,STATE>(m_Nwa);
		for (STATE initialState : m_Nwa.getInitialStates()) {
			detState.addPair(m_Nwa.getEmptyStackState(), initialState, m_Nwa);
		}
		updateMaxDegreeOfNondeterminism(detState.degreeOfNondeterminism());
		return detState;
	}
	
	
	@Override
	public DeterminizedState<LETTER,STATE> internalSuccessor(
			DeterminizedState<LETTER,STATE> detState,
			LETTER symbol) {
		
		DeterminizedState<LETTER,STATE> succDetState = 
				new DeterminizedState<LETTER,STATE>(m_Nwa);
		for (STATE downState : detState.getDownStates()) {
			for (STATE upState : detState.getUpStates(downState)) {
				for (OutgoingInternalTransition<LETTER, STATE> upSucc : m_Nwa.internalSuccessors(upState, symbol)) {
					succDetState.addPair(downState,upSucc.getSucc(), m_Nwa);
				}
			}
		}
		updateMaxDegreeOfNondeterminism(succDetState.degreeOfNondeterminism());
		return succDetState;	
	}
	


	@Override
	public DeterminizedState<LETTER,STATE> callSuccessor(
			DeterminizedState<LETTER,STATE> detState, 
			LETTER symbol) {
		
		DeterminizedState<LETTER,STATE> succDetState = 
				new DeterminizedState<LETTER,STATE>(m_Nwa);
		for (STATE downState : detState.getDownStates()) {
			for (STATE upState : detState.getUpStates(downState)) {
				for (OutgoingCallTransition<LETTER, STATE> upSucc : m_Nwa.callSuccessors(upState, symbol)) {
					STATE succDownState;
					// if !m_UseDoubleDeckers we always use getEmptyStackState()
					// as down state to obtain sets of states instead of
					// sets of DoubleDeckers.
					if (m_UseDoubleDeckers) {
						succDownState = upState;
					} else {
						succDownState = m_Nwa.getEmptyStackState();
					}
					succDetState.addPair(succDownState,upSucc.getSucc(), m_Nwa);
				}
			}
		}
		updateMaxDegreeOfNondeterminism(succDetState.degreeOfNondeterminism());
		return succDetState;	
	}

	

	@Override
	public DeterminizedState<LETTER,STATE> returnSuccessor(
			DeterminizedState<LETTER,STATE> detState,
			DeterminizedState<LETTER,STATE> detLinPred,
			LETTER symbol) {
		
		DeterminizedState<LETTER,STATE> succDetState = 
				new DeterminizedState<LETTER,STATE>(m_Nwa);
		
		for (STATE downLinPred : detLinPred.getDownStates()) {
			for (STATE upLinPred : detLinPred.getUpStates(downLinPred)) {
				Set<STATE> upStates;
				if (m_UseDoubleDeckers) {
					upStates = detState.getUpStates(upLinPred);
					if (upStates == null) continue;
				} else {
					assert detState.getDownStates().size() == 1;
					assert detState.getDownStates().iterator().next() == 
													m_Nwa.getEmptyStackState();
					// if !m_UseDoubleDeckers we always use getEmptyStackState()
					// as down state to obtain sets of states instead of
					// sets of DoubleDeckers.
					upStates = detState.getUpStates(m_Nwa.getEmptyStackState());
				}
				for (STATE upState : upStates) {
					for (OutgoingReturnTransition<LETTER, STATE> upSucc : m_Nwa.returnSucccessors(upState, upLinPred, symbol)) {
						assert m_UseDoubleDeckers || downLinPred == m_Nwa.getEmptyStackState();
						succDetState.addPair(downLinPred, upSucc.getSucc(), m_Nwa);
					}
				}
			}
		}
		updateMaxDegreeOfNondeterminism(succDetState.degreeOfNondeterminism());
		return succDetState;	
	}
	
	private void updateMaxDegreeOfNondeterminism(int newDegree) {
		if (newDegree > maxDegreeOfNondeterminism) {
			maxDegreeOfNondeterminism = newDegree;
		}
	}

	@Override
	public int getMaxDegreeOfNondeterminism() {
		return maxDegreeOfNondeterminism;
	}


	@Override
	public boolean useDoubleDeckers() {
		return m_UseDoubleDeckers;
	}


	@Override
	public STATE getState(DeterminizedState<LETTER, STATE> determinizedState) {
		return determinizedState.getContent(m_StateFactory);
	}
	
	
	
}
