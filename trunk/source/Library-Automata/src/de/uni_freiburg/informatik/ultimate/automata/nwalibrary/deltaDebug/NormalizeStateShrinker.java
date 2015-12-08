/*
 * Copyright (C) 2015 Christian Schilling <schillic@informatik.uni-freiburg.de>
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.deltaDebug;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;

/**
 * Normalizes state names.
 * 
 * This shrinker renames states in the following way:
 * - All initial states are named "q0_i" for some i.
 * - All other final states are named "qf_i" for some i.
 * - All other states are named "q_i" for some i.
 * 
 * For each of those three types of states the index is a consecutive number,
 * assigned in a depth-first manner starting from some initial state.
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public class NormalizeStateShrinker<LETTER, STATE>
		extends AShrinker<STATE, LETTER, STATE> {
	@SuppressWarnings("unchecked")
	@Override
	public INestedWordAutomaton<LETTER, STATE> createAutomaton(
			final List<STATE> list) {
		// create fresh automaton
		final INestedWordAutomaton<LETTER, STATE> automaton =
				m_factory.create();
		
		// remaining original states
		final HashSet<STATE> remaining =
				new HashSet<STATE>(m_automaton.getStates());
		final HashSet<STATE> toVisit = new HashSet<STATE>();
		final ArrayDeque<STATE> stack = new ArrayDeque<STATE>();
		for (final STATE state : list) {
			remaining.remove(state);
			if (m_automaton.isInitial(state)) {
				stack.add(state);
			} else {
				toVisit.add(state);
			}
		}
		
		// depth-first renaming of states
		final HashMap<STATE, STATE> old2new = new HashMap<STATE, STATE>();
		final HashSet<STATE> onStackOrVisited = new HashSet<STATE>(stack);
		int initials = 0;
		int finals = 0;
		int normals = 0;
		boolean firstRun = true;
		while (true) {
			if (stack.isEmpty()) {
				if (firstRun) {
					firstRun = false;
					stack.addAll(toVisit);
					onStackOrVisited.addAll(toVisit);
					stack.addAll(remaining);
					onStackOrVisited.addAll(remaining);
					continue;
				} else {
					break;
				}
			}
			final STATE oldState = stack.pop();
			final STATE newState;
			
			if (remaining.remove(oldState)) {
				// do not reassign this state name
				newState = oldState;
			} else {
				// assign new name
				assert (oldState instanceof String) :
					"The state was a string during list creation.";
				final String name;
				if (m_automaton.isInitial(oldState)) {
					name = "q0_" + ++initials;
				} else if (m_automaton.isFinal(oldState)) {
					name = "qf_" + ++finals;
				} else {
					name = "q_" + ++normals;
				}
				newState = (STATE) name;
			}
			
			old2new.put(oldState, newState);
			m_factory.addState(automaton, newState);
			
			// push successors which have not been visited
			for (final OutgoingInternalTransition<LETTER, STATE> trans :
					m_automaton.internalSuccessors(oldState)) {
				final STATE succ = trans.getSucc();
				if (! onStackOrVisited.contains(succ)) {
					stack.push(succ);
					onStackOrVisited.add(succ);
				}
			}
			for (final OutgoingCallTransition<LETTER, STATE> trans :
					m_automaton.callSuccessors(oldState)) {
				final STATE succ = trans.getSucc();
				if (! onStackOrVisited.contains(succ)) {
					stack.push(succ);
					onStackOrVisited.add(succ);
				}
			}
			for (final OutgoingReturnTransition<LETTER, STATE> trans :
					m_automaton.returnSuccessors(oldState)) {
				final STATE succ = trans.getSucc();
				if (! onStackOrVisited.contains(succ)) {
					stack.push(succ);
					onStackOrVisited.add(succ);
				}
			}
		}
		assert (automaton.size() == m_automaton.size()) :
			"The number of states must be retained.";
		
		// add transitions
		for (final Entry<STATE, STATE> entry : old2new.entrySet()) {
			final STATE oldState = entry.getKey();
			final STATE newState = entry.getValue();
			for (final OutgoingInternalTransition<LETTER, STATE> trans :
					m_automaton.internalSuccessors(oldState)) {
				m_factory.addInternalTransition(automaton, newState,
						trans.getLetter(), old2new.get(trans.getSucc()));
			}
			for (final OutgoingCallTransition<LETTER, STATE> trans :
					m_automaton.callSuccessors(oldState)) {
				m_factory.addCallTransition(automaton, newState,
						trans.getLetter(), old2new.get(trans.getSucc()));
			}
			for (final OutgoingReturnTransition<LETTER, STATE> trans :
					m_automaton.returnSuccessors(oldState)) {
				m_factory.addReturnTransition(automaton, newState,
						old2new.get(trans.getHierPred()), trans.getLetter(),
						old2new.get(trans.getSucc()));
			}
		}
		
		return automaton;
	}
	
	@Override
	public List<STATE> extractList() {
		final Set<STATE> states = m_automaton.getStates();
		final Iterator<STATE> iterator = states.iterator();
		if (iterator.hasNext()) {
			if (iterator.next() instanceof String) {
				// states of type string can be renamed
				return new ArrayList<STATE>(states);
			}
		}
		// no states or of non-string type cannot be renamed
		return new ArrayList<STATE>();
	}
}