/*
 * Copyright (C) 2020 Marcel Ebbinghaus
 * Copyright (C) 2020 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.Comparator;

/**
 * Interface used during depth-first search exploration of a finite automaton. This is for instance used by
 * {@link DepthFirstTraversal} and by sleep set reduction implementations.
 *
 * @author Marcel Ebbinghaus
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <S>
 *            The type of states in the automaton
 * @param <L>
 *            The type of letters in the automaton
 */
public interface IDfsOrder<L, S> {
	/**
	 * Given a state of a finite automaton, determines in which order its outgoing transitions shall be explored.
	 *
	 * @param state
	 *            the automaton state
	 * @return the order as a {@link Comparator}
	 */
	Comparator<L> getOrder(S state);

	/**
	 * Determines if the order is positional or not.
	 *
	 * @return true if the ordering may differ between states, false if it is guaranteed to be the same for all states.
	 */
	boolean isPositional();
}
