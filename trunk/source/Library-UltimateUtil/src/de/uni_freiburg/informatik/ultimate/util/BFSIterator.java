/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.util.ArrayDeque;
import java.util.Iterator;
import java.util.NoSuchElementException;

import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Performs breadth-first search through a graph and provides an iterator interface to the paths in the graph.
 *
 * This class cannot be used directly, but is meant to be used as a base class for more specialized iterators.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <V>
 *            the type of vertices in the graph
 * @param <E>
 *            the type of edges (or edge labels)
 * @param <X>
 *            the type of elements over which we iterate
 */
public abstract class BFSIterator<V, E, X> implements Iterator<X> {
	private final ArrayDeque<Pair<V, ImmutableList<Pair<V, E>>>> mQueue = new ArrayDeque<>();
	private X mNextElem;

	protected BFSIterator(final Iterable<V> initial) {
		for (final V init : initial) {
			mQueue.offer(new Pair<>(init, ImmutableList.empty()));
		}
	}

	protected abstract Iterable<E> getOutgoing(V vertex);

	protected abstract V getSuccessor(V vertex, E edge);

	protected abstract boolean isTarget(V vertex);

	protected abstract X finish(ImmutableList<Pair<V, E>> stack, V finalVertex);

	@Override
	public boolean hasNext() {
		if (mNextElem != null) {
			return true;
		}
		if (mQueue.isEmpty()) {
			return false;
		}

		searchNextElem();
		return mNextElem != null;
	}

	@Override
	public X next() {
		if (mNextElem == null) {
			searchNextElem();
		}
		if (mNextElem == null) {
			throw new NoSuchElementException();
		}

		final X result = mNextElem;
		mNextElem = null;
		return result;
	}

	private void searchNextElem() {
		assert mNextElem == null;

		while (!mQueue.isEmpty()) {
			final var candidate = mQueue.poll();
			final var vertex = candidate.getFirst();
			final var stack = candidate.getSecond();

			for (final var outgoing : getOutgoing(vertex)) {
				mQueue.offer(new Pair<>(getSuccessor(vertex, outgoing),
						new ImmutableList<>(new Pair<>(vertex, outgoing), stack)));
			}
			if (isTarget(vertex)) {
				mNextElem = finish(stack, vertex);
				return;
			}
		}
	}
}