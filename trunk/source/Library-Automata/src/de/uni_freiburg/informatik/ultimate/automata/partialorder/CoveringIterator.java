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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.lang.reflect.Array;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Spliterator;
import java.util.Spliterators;
import java.util.stream.IntStream;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Allows to enumerate a given word's covering words, or in case of symmetry, its equivalence class.
 *
 * Currently only supports unconditional independence.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters in the word.
 */
public final class CoveringIterator<L> implements Iterator<Word<L>> {
	private final Word<L> mWord;
	private final IIndependenceRelation<?, L> mIndependence;
	private final Class<L> mClazz;

	private final ArrayDeque<Pair<int[], ImmutableList<L>>> mStack = new ArrayDeque<>();
	private Word<L> mNextWord;

	private CoveringIterator(final Word<L> word, final IIndependenceRelation<?, L> independence, final Class<L> clazz) {
		mWord = word;
		mIndependence = independence;
		mClazz = clazz;
		mStack.push(new Pair<>(IntStream.range(0, mWord.length()).toArray(), ImmutableList.empty()));
	}

	/**
	 * Creates a stream enumerating all covering words for the given word.
	 *
	 * @param <L>
	 *            The type of letters
	 * @param word
	 *            The given word
	 * @param independence
	 *            An independence relation that determines covering. The relation may be symmetric or not, but currently
	 *            only unconditional independence is supported.
	 * @param clazz
	 *            the class object for the type of letters
	 * @return a stream containing exactly the words that cover the given word
	 */
	public static <L> Stream<Word<L>> enumerateCoveringWords(final Word<L> word,
			final IIndependenceRelation<?, L> independence, final Class<L> clazz) {
		assert !independence.isConditional() : "conditional independence is not yet supported";

		return StreamSupport.stream(Spliterators.spliteratorUnknownSize(
				new CoveringIterator<>(word, independence, clazz), Spliterator.ORDERED | Spliterator.IMMUTABLE), false);
	}

	@Override
	public boolean hasNext() {
		if (mNextWord != null) {
			return true;
		}
		if (mStack.isEmpty()) {
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
		while (!mStack.isEmpty()) {
			final var candidate = mStack.pop();

			final var prefix = candidate.getSecond();
			if (prefix.size() == mWord.length()) {
				mNextWord = makeWord(prefix);
				return;
			}

			final var positions = candidate.getFirst();
			if (positions.length < mWord.length() - prefix.size()) {
				continue;
			}

			for (final int i : positions) {
				final L letter = mWord.getSymbol(i);
				final int[] remainingPositions = Arrays.stream(positions).filter(j -> j != i && (i < j
						|| mIndependence.isIndependent(null, mWord.getSymbol(j), letter) == Dependence.INDEPENDENT))
						.toArray();
				mStack.push(new Pair<>(remainingPositions, new ImmutableList<>(letter, prefix)));
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
