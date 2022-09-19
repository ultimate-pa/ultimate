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

import java.lang.reflect.Array;
import java.util.ArrayDeque;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Spliterator;
import java.util.Spliterators;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.Word;
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
	public static <L> Iterable<Word<L>> enumerate(final INwaOutgoingTransitionProvider<L, ?> automaton,
			final Class<L> clazz) {
		return () -> new WordIterator<>(automaton, clazz);
	}

	public static <L> Stream<Word<L>> stream(final INwaOutgoingTransitionProvider<L, ?> automaton,
			final Class<L> clazz) {
		return StreamSupport.stream(Spliterators.spliteratorUnknownSize(new WordIterator<>(automaton, clazz),
				Spliterator.ORDERED | Spliterator.IMMUTABLE), false);
	}

	private static class WordIterator<L, S> implements Iterator<Word<L>> {
		private final INwaOutgoingTransitionProvider<L, S> mAutomaton;
		private final Class<L> mClazz;
		private final ArrayDeque<Pair<S, ImmutableList<L>>> mQueue = new ArrayDeque<>();

		private Word<L> mNextWord;

		public WordIterator(final INwaOutgoingTransitionProvider<L, S> automaton, final Class<L> clazz) {
			assert NestedWordAutomataUtils.isFiniteAutomaton(automaton) : "only finite automata are supported";

			mAutomaton = automaton;
			mClazz = clazz;
			for (final S init : mAutomaton.getInitialStates()) {
				mQueue.offer(new Pair<>(init, ImmutableList.empty()));
			}
		}

		@Override
		public boolean hasNext() {
			if (mNextWord != null) {
				return true;
			}
			if (mQueue.isEmpty()) {
				return false;
			}

			searchNextWord();
			return mNextWord != null;
		}

		@Override
		public Word<L> next() {
			if (mNextWord == null) {
				searchNextWord();
			}
			if (mNextWord == null) {
				throw new NoSuchElementException();
			}

			final Word<L> result = mNextWord;
			mNextWord = null;
			return result;
		}

		private void searchNextWord() {
			assert mNextWord == null;

			while (!mQueue.isEmpty()) {
				final var candidate = mQueue.poll();
				final var state = candidate.getFirst();
				final var word = candidate.getSecond();

				for (final var outgoing : mAutomaton.internalSuccessors(state)) {
					mQueue.offer(new Pair<>(outgoing.getSucc(), new ImmutableList<>(outgoing.getLetter(), word)));
				}
				if (mAutomaton.isFinal(state)) {
					mNextWord = makeWord(word);
					return;
				}
			}
		}

		private Word<L> makeWord(final ImmutableList<L> letters) {
			final L[] array = (L[]) Array.newInstance(mClazz, letters.size());
			int i = letters.size() - 1;
			for (final var letter : letters) {
				array[i] = letter;
				i--;
			}
			return new Word<>(array);
		}
	}

}
