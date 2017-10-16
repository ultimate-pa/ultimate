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
import java.util.Iterator;

public class IntSetBits implements IntSet {
	
	private BitSet mSet;
	
	public IntSetBits() {
		mSet = new BitSet();
	}

	@Override
	public IntIterator iterator() {
		return new SparseBitsIterator(this);
	}

	@Override
	public IntSet clone() {
		IntSetBits bits = new IntSetBits();
		bits.mSet = (BitSet) mSet.clone();
		return bits;
	}

	@Override
	public void andNot(IntSet set) {
		if(! (set instanceof IntSetBits)) {
			System.err.println("OPERAND should be BitSet");
			System.exit(-1);
		}
		BitSet bits = (BitSet) set.get();
		this.mSet.andNot(bits);
	}

	@Override
	public void and(IntSet set) {
		if(! (set instanceof IntSetBits)) {
			System.err.println("OPERAND should be BitSet");
			System.exit(-1);
		}
		BitSet bits = (BitSet) set.get();
		this.mSet.and(bits);
	}

	@Override
	public void or(IntSet set) {
		if(! (set instanceof IntSetBits)) {
			System.err.println("OPERAND should be BitSet");
			System.exit(-1);
		}
		BitSet bits = (BitSet) set.get();
		this.mSet.or(bits);		
	}

	@Override
	public boolean get(int value) {
		return mSet.get(value);
	}
	
	@Override
	public void set(int value) {
		mSet.set(value);
	}

	@Override
	public void clear(int value) {
		mSet.clear(value);
	}
	
	@Override
	public void clear() {
		mSet.clear();
	}

	@Override
	public boolean isEmpty() {
		return mSet.isEmpty();
	}

	@Override
	public int cardinality() {
		return mSet.cardinality();
	}
	
	@Override
	public boolean overlap(IntSet set) {
		if(! (set instanceof IntSetBits)) {
			System.err.println("OPERAND should be BitSet");
			System.exit(-1);
		}
		IntSetBits temp = (IntSetBits) set;
		return temp.mSet.intersects(this.mSet);
	}
	

	@Override
	public boolean subsetOf(IntSet set) {
		if(! (set instanceof IntSetBits)) {
			System.err.println("OPERAND should be BitSet");
			System.exit(-1);
		}
		BitSet temp = (BitSet) this.mSet.clone();
		BitSet bits = (BitSet) set.get();
		temp.andNot(bits);
		return temp.isEmpty();
	}

	@Override
	public boolean contentEq(IntSet set) {
		if(! (set instanceof IntSetBits)) {
			System.err.println("OPERAND should be BitSet");
			System.exit(-1);
		}
		BitSet bits = (BitSet) set.get();
		return this.mSet.equals(bits);
	}

	@Override
	public Object get() {
		return mSet;
	}
	
	@Override
	public String toString() {
		return mSet.toString();
	}
	
	public boolean equals(Object obj) {
		if(! (obj instanceof IntSetBits)) {
			System.err.println("OPERAND should be BitSet");
			System.exit(-1);
		}
		IntSetBits bits = (IntSetBits)obj;
		return this.contentEq(bits);
	}
	
	public static class SparseBitsIterator implements IntIterator {

		private BitSet mBits;
		private int mIndex;
		
		public SparseBitsIterator(IntSetBits set) {
			this.mBits = set.mSet;
			mIndex = mBits.nextSetBit(0);
		}
		
		public boolean hasNext() {
			return (mIndex >= 0);
		}
		
		public int next() {
			int rv = mIndex;
			mIndex = mBits.nextSetBit(mIndex + 1);
			return rv;
		}
	}
	
	@Override
	public Iterable<Integer> iterable() {
		return () -> new Iterator<Integer>() {
			IntIterator iter = iterator();
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
