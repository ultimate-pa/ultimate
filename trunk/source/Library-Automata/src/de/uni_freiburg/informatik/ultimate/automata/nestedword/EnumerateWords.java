/*
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import java.util.Spliterator;
import java.util.Spliterators;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.util.BFSIterator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Enumerates all words accepted by a given finite automaton, in increasing length.
 *
 * If the automaton is nondeterministic, words may be enumerated repeatedly.
 *
 * Call and return edges are not yet supported.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public final class EnumerateWords {
	public static <L> Iterable<Word<L>> enumerate(final INwaOutgoingTransitionProvider<L, ?> automaton) {
		return () -> new WordIterator<>(automaton);
	}

	public static <L> Stream<Word<L>> stream(final INwaOutgoingTransitionProvider<L, ?> automaton) {
		return StreamSupport.stream(Spliterators.spliteratorUnknownSize(new WordIterator<>(automaton),
				Spliterator.ORDERED | Spliterator.IMMUTABLE), false);
	}

	private static class WordIterator<L, S> extends BFSIterator<S, OutgoingInternalTransition<L, S>, Word<L>> {
		private final INwaOutgoingTransitionProvider<L, S> mAutomaton;

		public WordIterator(final INwaOutgoingTransitionProvider<L, S> automaton) {
			super(automaton.getInitialStates());
			assert NestedWordAutomataUtils.isFiniteAutomaton(automaton) : "only finite automata are supported";
			mAutomaton = automaton;
		}

		@Override
		protected Iterable<OutgoingInternalTransition<L, S>> getOutgoing(final S state) {
			return mAutomaton.internalSuccessors(state);
		}

		@Override
		protected S getSuccessor(final S state, final OutgoingInternalTransition<L, S> transition) {
			return transition.getSucc();
		}

		@Override
		protected boolean isTarget(final S state) {
			return mAutomaton.isFinal(state);
		}

		@Override
		protected Word<L> finish(final ImmutableList<Pair<S, OutgoingInternalTransition<L, S>>> stack,
				final S finalState) {
			final L[] letters = (L[]) new Object[stack.size()];
			int i = stack.size() - 1;
			for (final var frame : stack) {
				letters[i] = frame.getSecond().getLetter();
				i--;
			}
			return new Word<>(letters);
		}
	}
}
