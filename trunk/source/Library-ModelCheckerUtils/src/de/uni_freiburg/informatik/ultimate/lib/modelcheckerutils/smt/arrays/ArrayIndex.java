/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Represents a multi-dimensional array index which is a List of terms.
 *
 * @author Matthias Heizmann
 *
 */
public class ArrayIndex implements List<Term> {

	private final List<Term> mIndexEntries;


	public ArrayIndex() {
		mIndexEntries = Collections.emptyList();
	}

	public ArrayIndex(final List<Term> indexEntries) {
		mIndexEntries = indexEntries;
	}

	@Override
	public boolean add(final Term arg0) {
		throw new UnsupportedOperationException("ArrayIndex is immutable");
	}

	@Override
	public void add(final int arg0, final Term arg1) {
		throw new UnsupportedOperationException("ArrayIndex is immutable");
	}

	@Override
	public boolean addAll(final Collection<? extends Term> arg0) {
		throw new UnsupportedOperationException("ArrayIndex is immutable");
	}

	@Override
	public boolean addAll(final int arg0, final Collection<? extends Term> arg1) {
		throw new UnsupportedOperationException("ArrayIndex is immutable");
	}

	@Override
	public void clear() {
		throw new UnsupportedOperationException("ArrayIndex is immutable");
	}

	@Override
	public boolean contains(final Object arg0) {
		return mIndexEntries.contains(arg0);
	}

	@Override
	public boolean containsAll(final Collection<?> arg0) {
		return mIndexEntries.containsAll(arg0);
	}

	@Override
	public Term get(final int arg0) {
		return mIndexEntries.get(arg0);
	}

	@Override
	public int indexOf(final Object arg0) {
		return mIndexEntries.indexOf(arg0);
	}

	@Override
	public boolean isEmpty() {
		return mIndexEntries.isEmpty();
	}

	@Override
	public Iterator<Term> iterator() {
		return mIndexEntries.iterator();
	}

	@Override
	public int lastIndexOf(final Object arg0) {
		return mIndexEntries.lastIndexOf(arg0);
	}

	@Override
	public ListIterator<Term> listIterator() {
		return mIndexEntries.listIterator();
	}

	@Override
	public ListIterator<Term> listIterator(final int arg0) {
		return mIndexEntries.listIterator(arg0);
	}

	@Override
	public boolean remove(final Object arg0) {
		throw new UnsupportedOperationException("ArrayIndex is immutable");
	}

	@Override
	public Term remove(final int arg0) {
		throw new UnsupportedOperationException("ArrayIndex is immutable");
	}

	@Override
	public boolean removeAll(final Collection<?> arg0) {
		throw new UnsupportedOperationException("ArrayIndex is immutable");
	}

	@Override
	public boolean retainAll(final Collection<?> arg0) {
		throw new UnsupportedOperationException("ArrayIndex is immutable");
	}

	@Override
	public Term set(final int arg0, final Term arg1) {
		throw new UnsupportedOperationException("ArrayIndex is immutable");
	}

	@Override
	public int size() {
		return mIndexEntries.size();
	}

	@Override
	public List<Term> subList(final int arg0, final int arg1) {
		return mIndexEntries.subList(arg0, arg1);
	}

	@Override
	public Object[] toArray() {
		return mIndexEntries.toArray();
	}

	@Override
	public <T> T[] toArray(final T[] arg0) {
		return mIndexEntries.toArray(arg0);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mIndexEntries == null) ? 0 : mIndexEntries.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final ArrayIndex other = (ArrayIndex) obj;
		if (mIndexEntries == null) {
			if (other.mIndexEntries != null) {
				return false;
			}
		} else if (!mIndexEntries.equals(other.mIndexEntries)) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		return mIndexEntries.toString();
	}

	/**
	 * Functional-style append operation -- returns a new ArrayIndex object where the term is added.
	 */
	public ArrayIndex append(final Term term) {
		final List<Term> newList = new ArrayList<>(size() + 1);
		newList.addAll(mIndexEntries);
		newList.add(term);
		return new ArrayIndex(newList);
	}

	/**
	 * Returns an new {@link ArrayIndex} that consists of the first k entries of
	 * this index.
	 */
	public ArrayIndex getFirst(final int k) {
		final List<Term> indexEntries = new ArrayList<>();
		for (int i = 0; i < k; i++) {
			indexEntries.add(mIndexEntries.get(i));
		}
		return new ArrayIndex(indexEntries);
	}

	/**
	 * Returns an new {@link ArrayIndex} that consists of the last k entries of this
	 * index.
	 */
	public ArrayIndex getLast(final int k) {
		final List<Term> indexEntries = new ArrayList<>();
		for (int i = mIndexEntries.size() - k; i < mIndexEntries.size(); i++) {
			indexEntries.add(mIndexEntries.get(i));
		}
		return new ArrayIndex(indexEntries);
	}


	/**
	 * Returns the free variable of all entries.
	 */
	public Set<TermVariable> getFreeVars() {
		return SmtUtils.getFreeVars(mIndexEntries);
	}

	/**
	 * Returns true iff the free variables of all index terms are a subset of tvSet.
	 */
	public boolean freeVarsAreSubset(final Set<TermVariable> tvSet) {
		for (final Term term : mIndexEntries) {
			for (final TermVariable tv : term.getFreeVars()) {
				if (!tvSet.contains(tv)) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * Return a new {@link ArrayIndex} whose entries are the elements of
	 * newIndexEntries followed by the entries of this.
	 */
	public ArrayIndex appendEntriesAtBeginning(final List<Term> newIndexEntries) {
		final List<Term> resultEntries = new ArrayList<>(newIndexEntries);
		resultEntries.addAll(this);
		return new ArrayIndex(resultEntries);
	}

	/**
	 * Appends to each {@link ArrayIndex} in list indices the newIndexEntries. Does
	 * not modify existing objects but return new objects.
	 */
	public static List<ArrayIndex> appendEntriesAtBeginning(final List<ArrayIndex> indices,
			final List<Term> newIndexEntries) {
		final List<ArrayIndex> result = new ArrayList<>(indices.size());
		for (final ArrayIndex index : indices) {
			result.add(index.appendEntriesAtBeginning(newIndexEntries));
		}
		return result;
	}

}
