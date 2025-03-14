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

package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util;

import java.util.Iterator;

import gnu.trove.iterator.TIntIterator;
import gnu.trove.set.TIntSet;
import gnu.trove.set.hash.TIntHashSet;

public class IntSetTIntSet implements IntSet {

	private final TIntSet mSet;

	public IntSetTIntSet() {
		mSet = new TIntHashSet();
	}

	public IntSetTIntSet(final TIntSet set) {
		mSet = set;
	}

	@Override
	public IntIterator iterator() {
		return new TIntSetIterator(this);
	}

	@Override
	public IntSet clone() {
		final IntSetTIntSet copy = new IntSetTIntSet();
		copy.mSet.addAll(mSet);
		return copy;
	}

	@Override
	public void andNot(final IntSet set) {
		assert set instanceof IntSetTIntSet : "OPERAND should be TIntSet";
		final IntSetTIntSet temp = (IntSetTIntSet) set;
		mSet.removeAll(temp.mSet);
	}

	@Override
	public void and(final IntSet set) {
		assert set instanceof IntSetTIntSet : "OPERAND should be TIntSet";
		final IntSetTIntSet temp = (IntSetTIntSet) set;
		mSet.retainAll(temp.mSet);
	}

	@Override
	public void or(final IntSet set) {
		assert set instanceof IntSetTIntSet : "OPERAND should be TIntSet";
		final IntSetTIntSet temp = (IntSetTIntSet) set;
		mSet.addAll(temp.mSet);
	}

	@Override
	public boolean get(final int value) {
		return mSet.contains(value);
	}

	@Override
	public void set(final int value) {
		mSet.add(value);
	}

	@Override
	public void clear(final int value) {
		mSet.remove(value);
	}

	@Override
	public void clear() {
		mSet.clear();
	}

	@Override
	public String toString() {
		return mSet.toString();
	}

	@Override
	public boolean isEmpty() {
		return mSet.isEmpty();
	}

	@Override
	public int cardinality() {
		return mSet.size();
	}

	@Override
	public boolean subsetOf(final IntSet set) {
		assert set instanceof IntSetTIntSet : "OPERAND should be TIntSet";
		final IntSetTIntSet temp = (IntSetTIntSet) set;
		return temp.mSet.containsAll(mSet);
	}

	@Override
	public boolean contentEq(final IntSet set) {
		assert set instanceof IntSetTIntSet : "OPERAND should be TIntSet";
		final IntSetTIntSet temp = (IntSetTIntSet) set;
		return mSet.equals(temp.mSet);
	}

	@Override
	public Object get() {
		return mSet;
	}

	@Override
	public boolean equals(final Object obj) {
		if (obj == null || getClass() != obj.getClass()) {
			return false;
		}
		final IntSetTIntSet temp = (IntSetTIntSet) obj;
		return contentEq(temp);
	}

	@Override
	public int hashCode() {
		return mSet.hashCode();
	}

	public static class TIntSetIterator implements IntIterator {

		private final TIntIterator mSetIter;

		public TIntSetIterator(final IntSetTIntSet set) {
			mSetIter = set.mSet.iterator();
		}

		@Override
		public boolean hasNext() {
			return mSetIter.hasNext();
		}

		@Override
		public int next() {
			return mSetIter.next();
		}

	}

	@Override
	public Iterable<Integer> iterable() {
		return () -> new Iterator<>() {
			TIntIterator iter = mSet.iterator();

			@Override
			public boolean hasNext() {
				return iter.hasNext();
			}

			@Override
			public Integer next() {
				return iter.next();
			}

		};
	}

}
