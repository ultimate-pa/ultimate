/*
 * Copyright (C) 2017 Yong Li (liyong@ios.ac.cn)
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
 * Interface for the most basic data structure that represents a generalized nested word automaton (GNWA).
 * The acceptance is a list of sets of states, say [F1, F2, F3, ..., Fn], where n is the size of the acceptance
 * For instance, we have acceptance ({q1, q3}, {q4, q1}, {q3, q2}) for a GNWA, then
 *    getAcceptanceSize() == 3;
 *    isFinal(q1, 0) == true && isFinal(q1, 1) == true && isFinal(q1, 2) == false;
 *    getAcceptanceLabels(q1) == {0, 1} == { i | i \in [0..getAcceptanceSize()-1] and isFinal(q1, i)}
 * 
 * @author liyong
 * @param <LETTER>
 *            Type of objects which can be used as letters of the alphabet.
 * @param <STATE>
 *            Type of objects which can be used as states.
 */

public interface IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> extends INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> {
	
	/** get the size of generalized acceptance condition */
	int getAcceptanceSize();
	
	/** check whether state is in the index-th set of generalized acceptance */
	boolean isFinal(STATE state, int index);	
	
	@Override
	default boolean isFinal(final STATE state) {
		return !getAcceptanceLabels(state).isEmpty();
	}
	
	/** get the labels (the indices of accepting set) of state */
	Set<Integer> getAcceptanceLabels(STATE state);
	
}
