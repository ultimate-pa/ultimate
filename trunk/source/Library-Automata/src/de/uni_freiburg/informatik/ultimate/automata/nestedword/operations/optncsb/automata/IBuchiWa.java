/*
 * Copyright (C) 2017 Yong Li (liyong@ios.ac.cn)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntIterator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;

/**
 * Buchi word automata
 */
public interface IBuchiWa extends IBuchi<IStateWa> {

	default IntSet getSuccessors(final IntSet states, final int letter) {
		final IntSet result = UtilIntSet.newIntSet();
		for (final int state : states.iterable()) {
			result.or(getSuccessors(state, letter));
		}
		return result;
	}

	IntSet getSuccessors(int state, int letter);

	@Override
	void makeComplete();

	// use this function if automtaton is too large
	default void toBA(final PrintStream out, final List<String> alphabet) {
		final IntSet initialStates = getInitialStates();
		if (initialStates.cardinality() > 1) {
			throw new RuntimeException("BA format does not allow multiple initial states...");
		}
		final IntIterator iter = initialStates.iterator();
		out.print("[" + iter.next() + "]\n");
		// output automata in BA (RABIT format)
		final Collection<IStateWa> states = getStates();
		for (final IStateWa state : states) {
			state.toBA(out, alphabet);
		}
		for (final int fin : getFinalStates().iterable()) {
			out.print("[" + fin + "]\n");
		}
	}

	default String toBA() {
		final ByteArrayOutputStream out = new ByteArrayOutputStream();
		try {
			final List<String> alphabet = new ArrayList<>();
			for (int i = 0; i < getAlphabetSize(); i++) {
				alphabet.add(i + "");
			}
			toBA(new PrintStream(out), alphabet);
			return out.toString();
		} catch (final Exception e) {
			return "ERROR";
		}
	}

	@Override
	default int getTransitionSize() {
		int num = 0;
		for (final IStateWa s : getStates()) {
			for (final Integer letter : s.getEnabledLetters()) {
				num += s.getSuccessors(letter).cardinality();
			}
		}
		return num;
	}

	@Override
	default void toATS(final PrintStream out, final List<String> alphabet) {
		final String PRE_BLANK = "   ";
		final String ITEM_BLANK = " ";
		final String LINE_END = "},";
		final String BLOCK_END = "\n" + PRE_BLANK + "}";
		final String TRANS_PRE_BLANK = PRE_BLANK + "   ";
		out.println("FiniteAutomaton result = (");

		out.print(PRE_BLANK + "alphabet = {");
		for (int i = 0; i < getAlphabetSize(); i++) {
			out.print(alphabet.get(i) + ITEM_BLANK);
		}
		out.println(LINE_END);

		// states
		final Collection<IStateWa> states = getStates();
		out.print(PRE_BLANK + "states = {");
		for (final IStateWa state : states) {
			out.print("s" + state.getId() + ITEM_BLANK);
		}
		out.println(LINE_END);
		// initial states
		out.print(PRE_BLANK + "initialStates = {");
		for (final Integer id : getInitialStates().iterable()) {
			out.print("s" + id + ITEM_BLANK);
		}
		out.println(LINE_END);

		// final states
		out.print(PRE_BLANK + "finalStates = {");
		for (final Integer id : getFinalStates().iterable()) {
			out.print("s" + id + ITEM_BLANK);
		}
		out.println(LINE_END);

		// call transitions
		out.print(PRE_BLANK + "transitions = {");
		for (final IStateWa state : states) {
			for (final Integer letter : state.getEnabledLetters()) {
				for (final Integer succ : state.getSuccessors(letter).iterable()) {
					out.print("\n" + TRANS_PRE_BLANK + "(s" + state.getId() + " " + alphabet.get(letter) + " s" + succ
							+ ")");
				}
			}
		}
		out.println(BLOCK_END);

		out.println(");");
	}

	// a Buchi automaton is semideterministic if all transitions after the accepting states are deterministic
	@Override
	default boolean isSemiDeterministic() {
		final IntSet finIds = getFinalStates();
		final LinkedList<IStateWa> walkList = new LinkedList<>();

		// add to list
		IntIterator iter = finIds.iterator();
		while (iter.hasNext()) {
			walkList.addFirst(getState(iter.next()));
		}

		final IntSet visited = UtilIntSet.newIntSet();
		while (!walkList.isEmpty()) {
			final IStateWa s = walkList.remove();
			if (visited.get(s.getId())) {
				continue;
			}
			visited.set(s.getId());
			for (int i = 0; i < getAlphabetSize(); i++) {
				final IntSet succs = s.getSuccessors(i);
				if (succs.isEmpty()) {
					continue;
				}
				if (succs.cardinality() > 1) {
					return false;
				}

				iter = succs.iterator();
				final int succ = iter.next();
				if (!visited.get(succ)) {
					walkList.addFirst(getState(succ));
				}
			}
		}

		return true;
	}

	@Override
	default boolean isDeterministic(final int state) {
		final LinkedList<IStateWa> walkList = new LinkedList<>();

		walkList.addFirst(getState(state));

		final IntSet visited = UtilIntSet.newIntSet();
		while (!walkList.isEmpty()) {
			final IStateWa s = walkList.remove();
			if (visited.get(s.getId())) {
				continue;
			}
			visited.set(s.getId());
			for (int i = 0; i < getAlphabetSize(); i++) {
				final IntSet succs = s.getSuccessors(i);
				if (succs.cardinality() > 1) {
					return false;
				}
				if (succs.isEmpty()) {
					continue;
				}
				final IntIterator iter = succs.iterator();
				final int succ = iter.next();
				if (!visited.get(succ)) {
					walkList.addFirst(getState(succ));
				}
			}
		}

		return true;
	}

}
