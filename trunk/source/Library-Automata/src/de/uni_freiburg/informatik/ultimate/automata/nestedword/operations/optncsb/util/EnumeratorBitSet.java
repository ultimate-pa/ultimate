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

import java.util.BitSet;

/**
 * This is a helper class for enumerate all possible subsets in a given full BitSet
 */
class EnumeratorBitSet extends BitSet implements Comparable<EnumeratorBitSet> {

	private static final long serialVersionUID = 1L;
	/**
	 * should keep the size
	 */
	private final int size;

	public EnumeratorBitSet(final int size) {
		super(size);
		assert size > 0 : "valuation size should be positive number";
		this.size = size; // very important to know the size
	}

	@Override
	public int size() {
		return size;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || getClass() != obj.getClass()) {
			return false;
		}
		final EnumeratorBitSet other = (EnumeratorBitSet) obj;
		return compareTo(other) == 0;
	}

	@Override
	public EnumeratorBitSet clone() {
		final EnumeratorBitSet copy = new EnumeratorBitSet(size());
		copy.or(this);
		return copy;
	}

	@Override
	public int compareTo(final EnumeratorBitSet bits) {
		if (bits.size() > size()) {
			return -1;
		}
		if (bits.size() < size()) {
			return 1;
		}
		for (int i = 0; i < size(); i++) {
			if (get(i) && !bits.get(i)) {
				return 1;
			} else if (!get(i) && bits.get(i)) {
				return -1;
			}
		}
		return 0;
	}

	@Override
	public String toString() {
		return super.toString();
	}

	/** increase a bit */
	protected void nextBitSet() {
		final int i = nextClearBit(0);
		this.clear(0, i);
		this.set(i);
	}

	// since this is modifiable bitset, we donot supprt hashCode
	@Override
	public int hashCode() {
		throw new UnsupportedOperationException("EnumeratorBitSet doesnot support hashCode");
	}
}
