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

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;

/**
 * Removes states.
 * 
 * This shrinker removes any kind of states.
 * Especially, it does not make an exception to initial states.
 * Transitions are added iff all respective states are still present.
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public class StateShrinker<STATE, LETTER>
		extends AShrinker<STATE, LETTER, STATE> {
	@Override
	public INestedWordAutomaton<LETTER, STATE> createAutomaton(
			final List<STATE> states) {
		// create fresh automaton
		INestedWordAutomaton<LETTER, STATE> automaton = m_factory.create();
		
		// add the complement of the passed states
		final Set<STATE> oldStates =
				new HashSet<STATE>(m_automaton.getStates());
		oldStates.removeAll(states);
		m_factory.addStates(automaton, oldStates);
		
		// add transitions which still remain
		m_factory.addFilteredTransitions(automaton);
		
		// store automaton temporarily
		m_prevAutomaton = automaton;
		
		return automaton;
	}
	
	@Override
	public List<STATE> extractList() {
		return new ArrayList<STATE>(m_automaton.getStates());
	}
}