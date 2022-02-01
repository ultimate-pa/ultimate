/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Dennis Wölfing
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.xnf;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;

/**
 * Superclass for CNF and DNF.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 *
 * @param <E> type of the atoms
 */
public abstract class Xnf<E> implements Collection<Collection<E>> {

	private final Collection<Collection<E>> mOuterJuncts;

	public Xnf() {
		mOuterJuncts = new ArrayList<>();
	}

	public Xnf(final int initialCapacity) {
		mOuterJuncts = new ArrayList<>(initialCapacity);
	}

	public Xnf(final Collection<E> collection) {
		mOuterJuncts = Collections.singleton(collection);
	}

	@Override
	public boolean add(final Collection<E> e) {
		return mOuterJuncts.add(e);
	}

	@Override
	public boolean addAll(final Collection<? extends Collection<E>> c) {
		return mOuterJuncts.addAll(c);
	}

	@Override
	public void clear() {
		mOuterJuncts.clear();
	}

	@Override
	public boolean contains(final Object o) {
		return mOuterJuncts.contains(o);
	}

	@Override
	public boolean containsAll(final Collection<?> c) {
		return mOuterJuncts.containsAll(c);
	}

	@Override
	public boolean equals(final Object o) {
		return mOuterJuncts.equals(o);
	}

	@Override
	public int hashCode() {
		return mOuterJuncts.hashCode();
	}

	@Override
	public boolean isEmpty() {
		return mOuterJuncts.isEmpty();
	}

	@Override
	public Iterator<Collection<E>> iterator() {
		return mOuterJuncts.iterator();
	}

	@Override
	public boolean remove(final Object o) {
		return mOuterJuncts.remove(o);
	}

	@Override
	public boolean removeAll(final Collection<?> c) {
		return mOuterJuncts.removeAll(c);
	}

	@Override
	public boolean retainAll(final Collection<?> c) {
		return mOuterJuncts.retainAll(c);
	}

	@Override
	public int size() {
		return mOuterJuncts.size();
	}

	@Override
	public Object[] toArray() {
		return mOuterJuncts.toArray();
	}

	@Override
	public <T> T[] toArray(final T[] a) {
		return mOuterJuncts.toArray(a);
	}

	@Override
	public String toString() {
		return mOuterJuncts.toString();
	}


}
