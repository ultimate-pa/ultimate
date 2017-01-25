/*
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

/**
 * undocumented!
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @deprecated Do not use this old API anymore.
 * @see INestedWordAutomatonSimple
 * @see INestedWordAutomaton
 */
@Deprecated
public interface INestedWordAutomatonOldApi<LETTER, STATE> extends INestedWordAutomaton<LETTER, STATE> {
	
	/**
	 * Internal successors.
	 * 
	 * @param state
	 *            state
	 * @param letter
	 *            letter
	 * @return All states succ such that state has an outgoing
	 *         internal transition (state, letter, succ)
	 */
	Iterable<STATE> succInternal(STATE state, LETTER letter);
	
	/**
	 * Call successors.
	 * 
	 * @param state
	 *            state
	 * @param letter
	 *            letter
	 * @return All states succ such that state has an outgoing
	 *         call transition (state, letter, succ)
	 */
	Iterable<STATE> succCall(STATE state, LETTER letter);
	
	/**
	 * Return successors.
	 * 
	 * @param state
	 *            state
	 * @param hier
	 *            hierarchical predecessor
	 * @param letter
	 *            letter
	 * @return All states succ such that state has an outgoing
	 *         return transition (state, hier, letter, succ)
	 */
	Iterable<STATE> succReturn(STATE state, STATE hier, LETTER letter);
	
	/**
	 * Internal predecessors.
	 * 
	 * @param state
	 *            state
	 * @param letter
	 *            letter
	 * @return All states pred such that there is an incoming
	 *         internal transition (pred, letter, state)
	 */
	Iterable<STATE> predInternal(STATE state, LETTER letter);
	
	/**
	 * Call predecessors.
	 * 
	 * @param state
	 *            state
	 * @param letter
	 *            letter
	 * @return All states pred such that there is an incoming
	 *         call transition (pred, letter, state)
	 */
	Iterable<STATE> predCall(STATE state, LETTER letter);
	
}
