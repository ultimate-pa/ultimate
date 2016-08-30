/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.util.Set;

/**
 * A nested word automaton interface which provides additional information about {@link DoubleDecker}s.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @see INestedWordAutomaton
 * @see DoubleDecker
 */
public interface IDoubleDeckerAutomaton<LETTER, STATE> extends INestedWordAutomaton<LETTER, STATE> {
	/**
	 * Provides the information whether there is a reachable configuration in which the automaton is in state
	 * <tt>upState</tt> and the state <tt>downState</tt> is the topmost stack element, resp. the current hierarchical
	 * predecessor.
	 * 
	 * @param upState
	 *            up state
	 * @param downState
	 *            down state
	 * @return true iff <tt>(upState, downState)</tt> forms a {@link DoubleDecker}
	 */
	boolean isDoubleDecker(STATE upState, STATE downState);
	
	/**
	 * Provides all states <tt>downState</tt> such that <tt>(upState, downState)</tt> is a {@link DoubleDecker}.
	 * 
	 * @param upState
	 *            up state
	 * @return all down states of <tt>upState</tt>
	 * @deprecated Use the {@link #isDoubleDecker(Object, Object) isDoubleDecker(up, down)} check instead.
	 */
	@Deprecated
			Set<STATE> getDownStates(STATE upState);
}
