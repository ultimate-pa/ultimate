/*
 * Copyright (C) 2016-2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * {@link HashRelation} implementation of a set of pairs.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <E>
 *            element type
 */
public class HashRelationBackedSetOfPairs<E> implements ISetOfPairs<E, HashRelation<E, E>> {
	private final HashRelation<E, E> mRelation;

	/**
	 * Constructor.
	 */
	public HashRelationBackedSetOfPairs() {
		mRelation = new HashRelation<>();
	}

	/**
	 * Note: Two calls to this method result in different {@link Pair} objects.
	 * <p>
	 * {@inheritDoc}
	 */
	@Override
	public Iterator<Pair<E, E>> iterator() {
		return new IteratorFromHashRelation<>(mRelation);
	}

	@Override
	public void addPair(final E lhs, final E rhs) {
		mRelation.addPair(lhs, rhs);
	}

	@Override
	public boolean containsPair(final E lhs, final E rhs) {
		return mRelation.containsPair(lhs, rhs);
	}

	@Override
	public HashRelation<E, E> getRelation() {
		return mRelation;
	}

	/**
	 * Iterator wrapper.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 * @param <E>
	 *            element type
	 */
	private static final class IteratorFromHashRelation<E> implements Iterator<Pair<E, E>> {
		private final Iterator<Entry<E, E>> mIt;

		public IteratorFromHashRelation(final HashRelation<E, E> hashRelation) {
			mIt = hashRelation.entrySet().iterator();
		}

		@Override
		public boolean hasNext() {
			return mIt.hasNext();
		}

		@Override
		public Pair<E, E> next() {
			final Entry<E, E> next = mIt.next();
			return new Pair<>(next.getKey(), next.getValue());
		}
	}

	@Override
	public String toString() {
		return mRelation.toString();
	}
}
