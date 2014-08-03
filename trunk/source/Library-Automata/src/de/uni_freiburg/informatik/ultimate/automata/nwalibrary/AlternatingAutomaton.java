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

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;

public class AlternatingAutomaton<LETTER, STATE> implements IAutomaton<LETTER, STATE> {
	
	/**
	 * Set of transitions PREs x LETTERs x SUCCs stored as map
	 * PREs -> LETTERs -> SUCCs
	 * The keySet of this map is used to store the set of states of this
	 * automaton.
	 */
	private Map<STATE,Map<LETTER,Set<STATE>>> m_TransitionsOut =
			new HashMap<STATE,Map<LETTER,Set<STATE>>>();
	
	/**
	 * Set of transitions PREs x LETTERs x SUCCs stored as map
	 * SUCCs -> LETTERs -> PREs
	 */
	private Map<STATE,Map<LETTER,Set<STATE>>> m_TransitionsIn =
			new HashMap<STATE,Map<LETTER,Set<STATE>>>();
	
	private Set<LETTER> m_Alphabet;
	
	protected final StateFactory<STATE> m_StateFactory;
	
	private Set<STATE> m_InitialStates = new HashSet<STATE>();
	private Set<STATE> m_FinalStates = new HashSet<STATE>();
	private Set<STATE> m_ExistentialStates = new HashSet<STATE>();
	private Set<STATE> m_UniversalStates = new HashSet<STATE>();
	
	public AlternatingAutomaton(Set<LETTER> alphabet,
			StateFactory<STATE> stateFactory) {
		if (alphabet == null) {
			throw new IllegalArgumentException("aa must have alphabet");
		}
		if (stateFactory == null) {
			throw new IllegalArgumentException("aa must have stateFactory");
		}
		this.m_Alphabet = alphabet;
		this.m_StateFactory = stateFactory;
	}
	
	boolean contains(STATE state) {
		return m_TransitionsOut.containsKey(state);
	}
	
	public void addTransition(STATE pred, LETTER letter, STATE succ) {
		if (!contains(pred)) {
			throw new IllegalArgumentException("State " + pred + " not in automaton");
		}
		assert contains(pred) : "State " + pred + " not in automaton";
		assert contains(succ) : "State " + succ + " not in automaton";
		Map<LETTER, Set<STATE>> letter2succs = m_TransitionsOut.get(pred);
		if (letter2succs == null) {
			letter2succs = new HashMap<LETTER, Set<STATE>>();
			m_TransitionsOut.put(pred, letter2succs);
		}
		Set<STATE> succs = letter2succs.get(letter);
		if (succs == null) {
			succs = new HashSet<STATE>();
			letter2succs.put(letter,succs);
		}
		succs.add(succ);
		
		Map<LETTER, Set<STATE>> letter2preds = m_TransitionsIn.get(succ);
		if (letter2preds == null) {
			letter2preds = new HashMap<LETTER, Set<STATE>>();
			m_TransitionsIn.put(succ, letter2preds);
		}
		Set<STATE> preds = letter2preds.get(letter);
		if (preds == null) {
			preds = new HashSet<STATE>();
			letter2preds.put(letter,preds);
		}
		preds.add(pred);
		// assert checkTransitionsStoredConsistent();
	}
	
	@Override
	public Set<LETTER> getAlphabet() {
		return m_Alphabet;
	}
	
	
	
	public Collection<STATE> getStates() {
		return this.m_TransitionsOut.keySet();
	}
	
	public Map<STATE,Map<LETTER,Set<STATE>>> getTransitionsMap() {
		return m_TransitionsOut;
		
	}
	
	
	@Override
	public int size() {
		return m_TransitionsOut.size();
	}


	@Override
	public String sizeInformation() {
		// TODO Auto-generated method stub
		return null;
	}
	

	public Set<STATE> getInitialStates() {
		return m_InitialStates;
	}
	
	public Set<STATE> getExistentialStates() {
		return m_ExistentialStates;
	}
	
	public Set<STATE> getUniversalStates() {
		return m_UniversalStates;
	}
	
	public Set<STATE> getFinalStates() {
		return m_FinalStates;
	}
	

	public void addState(boolean isInitial, boolean isFinal, boolean isExistential, STATE state) {
		assert (state != null);
		if (m_TransitionsOut.containsKey(state)) {
			throw new IllegalArgumentException("State already exists");
		}
		assert (!m_TransitionsIn.containsKey(state));
		//FIXME others
		m_TransitionsOut.put(state, null);
		
		if (isInitial) {
			m_InitialStates.add(state);
		}
		if (isFinal) {
			m_FinalStates.add(state);
		}
		if (isExistential) {
			m_ExistentialStates.add(state);
		} else {
			m_UniversalStates.add(state);
		}
		
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		return m_StateFactory;
	}

}
