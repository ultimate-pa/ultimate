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

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * {@link NestedMap2} implementation of a set of pairs.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <E>
 *            element type
 */
public class NestedMapBackedSetOfPairs<E> implements ISetOfPairs<E, NestedMap2<E, E, Pair<E, E>>> {
	private final NestedMap2<E, E, Pair<E, E>> mRelation;

	/**
	 * Constructor.
	 */
	public NestedMapBackedSetOfPairs() {
		mRelation = new NestedMap2<>();
	}

	/**
	 * Note: Two calls to this method result in the same {@link Pair} objects.
	 * <p>
	 * {@inheritDoc}
	 */
	@Override
	public Iterator<Pair<E, E>> iterator() {
		return mRelation.keys2().iterator();
	}

	@Override
	public void addPair(final E lhs, final E rhs) {
		mRelation.put(lhs, rhs, new Pair<>(lhs, rhs));
	}

	@Override
	public boolean containsPair(final E lhs, final E rhs) {
		return mRelation.get(lhs).containsKey(rhs);
	}

	@Override
	public NestedMap2<E, E, Pair<E, E>> getRelation() {
		return mRelation;
	}

	@Override
	public String toString() {
		return mRelation.toString();
	}
}
