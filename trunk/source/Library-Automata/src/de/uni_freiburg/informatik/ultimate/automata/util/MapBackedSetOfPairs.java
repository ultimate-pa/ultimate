/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.util;

import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.MapToCollectionIterator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Map implementation of a set of pairs.
 * <p>
 * The {@link #iterator()} method creates the {@link Pair} objects on-demand and does not store them. Accordingly, two
 * iterations would result in different {@link Pair} objects.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <E>
 *            element type
 */
public class MapBackedSetOfPairs<E> implements ISetOfPairs<E, Map<E, Set<E>>> {
	private final Map<E, Set<E>> mMap;

	/**
	 * @param map
	 *            Map.
	 */
	public MapBackedSetOfPairs(final Map<E, Set<E>> map) {
		mMap = map;
	}

	@Override
	public void addPair(final E lhs, final E rhs) {
		throw new UnsupportedOperationException("The pairs must be specified at construction time.");
	}

	@Override
	public boolean containsPair(final E lhs, final E rhs) {
		final Set<E> rhsSet = mMap.get(lhs);
		if (rhsSet == null) {
			return false;
		}
		return rhsSet.contains(rhs);
	}

	@Override
	public Map<E, Set<E>> getRelation() {
		return mMap;
	}

	/**
	 * Note: Two calls to this method result in different {@link Pair} objects.
	 * <p>
	 * {@inheritDoc}
	 */
	@Override
	public Iterator<Pair<E, E>> iterator() {
		final Map<E, Set<E>> map = mMap;
		return new Iterator<Pair<E, E>>() {
			private final MapToCollectionIterator<E, E, Set<E>> mIt = new MapToCollectionIterator<>(map);

			@Override
			public boolean hasNext() {
				return mIt.hasNext();
			}

			@Override
			public Pair<E, E> next() {
				final Entry<E, E> next = mIt.next();
				return new Pair<>(next.getKey(), next.getValue());
			}
		};
	}

	@Override
	public String toString() {
		return mMap.toString();
	}
}
