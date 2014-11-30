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

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

public class DeterminizeNwa<LETTER, STATE> implements INestedWordAutomatonSimple<LETTER, STATE> {
	
	private final IUltimateServiceProvider m_Services;
	
	private final INestedWordAutomatonSimple<LETTER, STATE> m_Operand;
	private final NestedWordAutomaton<LETTER, STATE> m_Cache;
	private final IStateDeterminizer<LETTER, STATE> m_StateDeterminizer;
	private final StateFactory<STATE> m_StateFactory;
	
	private final Map<STATE,DeterminizedState<LETTER, STATE>> m_res2det =
			new HashMap<STATE,DeterminizedState<LETTER, STATE>>();
	private final Map<DeterminizedState<LETTER, STATE>, STATE> m_det2res =
			new HashMap<DeterminizedState<LETTER, STATE>, STATE>();
	
	public DeterminizeNwa(IUltimateServiceProvider services,
			INestedWordAutomatonSimple<LETTER, STATE> operand, 
			IStateDeterminizer<LETTER, STATE> stateDeterminizer, 
			StateFactory<STATE> sf) {
		m_Services = services;
		m_Operand = operand;
		m_StateDeterminizer = stateDeterminizer;
		m_StateFactory = sf;
		m_Cache = new NestedWordAutomaton<LETTER, STATE>(m_Services, operand.getInternalAlphabet(), 
				operand.getCallAlphabet(), operand.getReturnAlphabet(), sf);

	}
	
	private void constructInitialState() {
		DeterminizedState<LETTER, STATE> initialDet = 
				m_StateDeterminizer.initialState();
		STATE initialState = m_StateDeterminizer.getState(initialDet);
		m_det2res.put(initialDet, initialState);
		m_res2det.put(initialState, initialDet);
		m_Cache.addState(true, initialDet.containsFinal(), initialState);
	}
	
	private STATE getOrConstructState(DeterminizedState<LETTER, STATE> detState) {
		STATE state = m_det2res.get(detState);
		if (state == null) {
			state = m_StateDeterminizer.getState(detState);
			m_det2res.put(detState, state);
			m_res2det.put(state, detState);
			m_Cache.addState(false, detState.containsFinal(), state);
		}
		return state;
	}
	
	
	
	public Collection<STATE> succInternal(STATE state, LETTER letter) {
		Collection<STATE> succs = m_Cache.succInternal(state, letter);
		if (succs == null) {
			DeterminizedState<LETTER, STATE> detState = m_res2det.get(state);
			assert (detState != null);
			DeterminizedState<LETTER, STATE> detSucc = 
					m_StateDeterminizer.internalSuccessor(detState, letter);
			STATE succ = getOrConstructState(detSucc);
			m_Cache.addInternalTransition(state, letter, succ);
		}
		return m_Cache.succInternal(state, letter);
	}

	public Collection<STATE> succCall(STATE state, LETTER letter) {
		Collection<STATE> succs = m_Cache.succCall(state, letter);
		if (succs == null) {
			DeterminizedState<LETTER, STATE> detState = m_res2det.get(state);
			assert (detState != null);
			DeterminizedState<LETTER, STATE> detSucc = 
					m_StateDeterminizer.callSuccessor(detState, letter);
			STATE succ = getOrConstructState(detSucc);
			m_Cache.addCallTransition(state, letter, succ);
		}
		return m_Cache.succCall(state, letter);
	}

	public Collection<STATE> succReturn(STATE state, STATE hier, LETTER letter) {
		Collection<STATE> succs = m_Cache.succReturn(state, hier, letter);
		if (succs == null) {
			DeterminizedState<LETTER, STATE> detState = m_res2det.get(state);
			assert (detState != null);
			DeterminizedState<LETTER, STATE> detHier = m_res2det.get(hier);
			assert (detHier != null);
			DeterminizedState<LETTER, STATE> detSucc = 
					m_StateDeterminizer.returnSuccessor(detState, detHier, letter);
			STATE succ = getOrConstructState(detSucc);
			m_Cache.addReturnTransition(state, hier, letter, succ);
		}
		return m_Cache.succReturn(state, hier, letter);
	}
	
	
	
	
	
	@Override
	public Iterable<STATE> getInitialStates() {
		if (m_Cache.getInitialStates().isEmpty()) {
			constructInitialState();
		}
		return m_Cache.getInitialStates();
	}


	@Override
	public Set<LETTER> getInternalAlphabet() {
		return m_Operand.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> getCallAlphabet() {
		return m_Operand.getCallAlphabet();
	}

	@Override
	public Set<LETTER> getReturnAlphabet() {
		return m_Operand.getReturnAlphabet();
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		return m_StateFactory;
	}
	
	@Override
	public boolean isInitial(STATE state) {
		return m_Cache.isInitial(state);
	}

	@Override
	public boolean isFinal(STATE state) {
		return m_Cache.isFinal(state);
	}



	@Override
	public STATE getEmptyStackState() {
		return m_Cache.getEmptyStackState();
	}

	@Override
	public Set<LETTER> lettersInternal(STATE state) {
		return m_Operand.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> lettersCall(STATE state) {
		return m_Operand.getCallAlphabet();
	}

	@Override
	public Set<LETTER> lettersReturn(STATE state) {
		return m_Operand.getReturnAlphabet();
	}


	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state, LETTER letter) {
		Collection<STATE> succs = m_Cache.succInternal(state, letter);
		if (succs == null || succs.isEmpty()) {
			DeterminizedState<LETTER, STATE> detState = m_res2det.get(state);
			assert (detState != null);
			DeterminizedState<LETTER, STATE> detSucc = 
					m_StateDeterminizer.internalSuccessor(detState, letter);
			STATE succ = getOrConstructState(detSucc);
			m_Cache.addInternalTransition(state, letter, succ);
		}
		return m_Cache.internalSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state) {
		for (LETTER letter : getInternalAlphabet()) {
			internalSuccessors(state, letter);
		}
		return m_Cache.internalSuccessors(state);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state, LETTER letter) {
		Collection<STATE> succs = m_Cache.succCall(state, letter);
		if (succs == null || succs.isEmpty()) {
			DeterminizedState<LETTER, STATE> detState = m_res2det.get(state);
			assert (detState != null);
			DeterminizedState<LETTER, STATE> detSucc = 
					m_StateDeterminizer.callSuccessor(detState, letter);
			STATE succ = getOrConstructState(detSucc);
			m_Cache.addCallTransition(state, letter, succ);
		}
		return m_Cache.callSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state) {
		for (LETTER letter : getCallAlphabet()) {
			callSuccessors(state, letter);
		}
		return m_Cache.callSuccessors(state);
	}



	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(
			STATE state, STATE hier, LETTER letter) {
		Collection<STATE> succs = m_Cache.succReturn(state, hier, letter);
		if (succs == null || succs.isEmpty()) {
			DeterminizedState<LETTER, STATE> detState = m_res2det.get(state);
			assert (detState != null);
			DeterminizedState<LETTER, STATE> detHier = m_res2det.get(hier);
			assert (detHier != null);
			DeterminizedState<LETTER, STATE> detSucc = 
					m_StateDeterminizer.returnSuccessor(detState, detHier, letter);
			STATE succ = getOrConstructState(detSucc);
			m_Cache.addReturnTransition(state, hier, letter, succ);
		}
		return m_Cache.returnSucccessors(state, hier, letter);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			STATE state, STATE hier) {
		for (LETTER letter : getReturnAlphabet()) {
			returnSucccessors(state, hier, letter);
		}
		return m_Cache.returnSuccessorsGivenHier(state, hier);
	}

	@Override
	public int size() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Set<LETTER> getAlphabet() {
		throw new UnsupportedOperationException();	}

	@Override
	public String sizeInformation() {
		return "size Information not available";
	}


}
