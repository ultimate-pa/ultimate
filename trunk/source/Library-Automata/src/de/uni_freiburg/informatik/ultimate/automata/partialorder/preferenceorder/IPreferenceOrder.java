/*
 * Copyright (C) 2022 Marcel Ebbinghaus
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder.preferenceorder;

import java.util.Comparator;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;

/**
 * Interface for (positional, monitor-based) lexicographic preference orders, used in partial order reduction.
 *
 * A preference order is an ordering on the words over some alphabet. Its purpose is to indicate a preference regarding
 * which interleavings should preferably be included as representatives in a reduction of some language (usually, the
 * error traces of a program). When combined with an independence relation, a preference order defines a particular
 * reduction: namely, the reduction where the minimal words (wrt. the preference order) of each equivalence class are
 * kept and all other words in the equivalence class are removed. (This definition of the reduction can be similarly
 * extended to semi-commutativity relations.)
 *
 * We primarily use lexicographic preference orders, as the resulting reduction can be effectively constructed using
 * e.g. the sleep set technique. The orders represented by this interface are a generalization of the classic
 * lexicographic orders, in so far as the underlying order on the alphabet is allowed to change depending on the prefix
 * of the word up to the letters being compared. We have two mechanisms to allow the order to change:
 * <ul>
 * <li>First, the order on the alphabet may differ depending on the current state of the reduced automaton (the program)
 * reached by the prefix. If that is the case, we say the order is <em>positional</em>.</li>
 * <li>Second, the preference order may be equipped with an additional total deterministic finite automaton over the
 * program alphabet, and the order on the alphabet may differ depending on the current state of this <em>monitor</em>
 * automaton reached by the prefix. If that is the case, we say the order is <em>monitor-based</em>.</li>
 * </ul>
 *
 * Generally, implementations of this interface may represent partial (i.e. non-total) orders on words. However, this
 * may lead to non-minimal reductions. It is recommended to totalize a preference order before using it to compute a
 * reduction.
 *
 * @param <L>
 *            letter type
 * @param <S1>
 *            program state type
 * @param <S2>
 *            monitor state type
 */
public interface IPreferenceOrder<L, S1, S2> {
	/**
	 * Determines the order on the program alphabet to be used after any prefix word which reaches the given states in
	 * the program resp. the monitor automaton.
	 *
	 * The returned order may be a partial order. In Java terminology, it does not have to be <em>consistent with
	 * {@code equals()}</em>.
	 *
	 * Multiple invocations with the same arguments must return comparators that are equal (according to their
	 * {@code equals()} method) to each other, though they do not have to be the same instance. Moreover, to achieve
	 * good performance, the same should hold for equally-behaving comparators returned for different arguments.
	 *
	 * @param programState
	 *            the state reached in the program
	 * @param monitorState
	 *            the state reached in the monitor automaton returned by {@link #getMonitor()}, if {@link #getMonitor()}
	 *            does not return {@code null}. Otherwise, this parameter is always {@code null}.
	 * @return the order on the alphabet
	 */
	Comparator<L> getOrder(S1 programState, S2 monitorState);

	/**
	 * Determines if the ordering returned by {@link #getOrder(S1, S2)} may differ depending on the supplied program
	 * state or not.
	 *
	 * Note that the order may still vary depending on the monitor state, if the order has a monitor automaton (see
	 * {@link #getMonitor()}) the order is positional or not.
	 *
	 * @return {@code true} if the order is positional, {@code false} otherwise.
	 */
	boolean isPositional();

	/**
	 * Retrieves the monitor automaton, if this instance is a monitor-based lexicographic preference order.
	 *
	 * The monitor automaton must be a total deterministic finite automaton, i.e., every state must have exactly one
	 * outgoing (internal) transition for every letter in the alphabet. It must not have call or return transitions.
	 *
	 * Multiple calls to this method must return the same instance.
	 *
	 * @return the monitor automaton, or {@code null} if this instance is not monitor-based
	 */
	INwaOutgoingLetterAndTransitionProvider<L, S2> getMonitor();
}
