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
/*
import com.zaxxer.sparsebits.SparseBitSet;

public class IntSetSparseBits implements IntSet {
	
	private SparseBitSet set;
	
	public IntSetSparseBits() {
		set = new SparseBitSet();
	}

	@Override
	public IntIterator iterator() {
		return new SparseBitsIterator(this);
	}

	@Override
	public IntSet clone() {
		IntSetSparseBits bits = new IntSetSparseBits();
		bits.set = set.clone();
		return bits;
	}

	@Override
	public void andNot(IntSet set) {
		if(! (set instanceof IntSetSparseBits)) {
			System.err.println("OPERAND should be SparseBitSet");
			System.exit(-1);
		}
		SparseBitSet bits = (SparseBitSet) set.get();
		this.set.andNot(bits);
	}

	@Override
	public void and(IntSet set) {
		if(! (set instanceof IntSetSparseBits)) {
			System.err.println("OPERAND should be SparseBitSet");
			System.exit(-1);
		}
		SparseBitSet bits = (SparseBitSet) set.get();
		this.set.and(bits);
	}

	@Override
	public void or(IntSet set) {
		if(! (set instanceof IntSetSparseBits)) {
			System.err.println("OPERAND should be SparseBitSet");
			System.exit(-1);
		}
		SparseBitSet bits = (SparseBitSet) set.get();
		this.set.or(bits);		
	}

	@Override
	public boolean get(int value) {
		return set.get(value);
	}
	
	@Override
	public void set(int value) {
		set.set(value);
	}

	@Override
	public void clear(int value) {
		set.clear(value);
	}
	
	@Override
	public void clear() {
		set.clear();
	}

	@Override
	public boolean isEmpty() {
		return set.isEmpty();
	}

	@Override
	public int cardinality() {
		return set.cardinality();
	}

	@Override
	public boolean overlap(IntSet set) {
		if(! (set instanceof IntSetSparseBits)) {
			System.err.println("OPERAND should be BitSet");
			System.exit(-1);
		}
		IntSetSparseBits temp = (IntSetSparseBits)set;
		return temp.set.intersects(this.set);
	}
	
	@Override
	public boolean subsetOf(IntSet set) {
		if(! (set instanceof IntSetSparseBits)) {
			System.err.println("OPERAND should be SparseBitSet");
			System.exit(-1);
		}
		SparseBitSet temp = this.set.clone();
		SparseBitSet bits = (SparseBitSet) set.get();
		temp.andNot(bits);
		return temp.isEmpty();
	}

	@Override
	public boolean contentEq(IntSet set) {
		if(! (set instanceof IntSetSparseBits)) {
			System.err.println("OPERAND should be SparseBitSet");
			System.exit(-1);
		}
		SparseBitSet bits = (SparseBitSet) set.get();
		return this.set.equals(bits);
	}

	@Override
	public String toString() {
		return set.toString();
	}
	
	@Override
	public Object get() {
		return set;
	}
	
	public boolean equals(Object obj) {
		if(! (obj instanceof IntSetSparseBits)) {
			System.err.println("OPERAND should be SparseBitSet");
			System.exit(-1);
		}
		IntSetSparseBits bits = (IntSetSparseBits)obj;
		return this.contentEq(bits);
	}
	
	public static class SparseBitsIterator implements IntIterator {

		private SparseBitSet bits;
		private int index;
		
		public SparseBitsIterator(IntSetSparseBits set) {
			this.bits = set.set;
			index = bits.nextSetBit(0);
		}
		
		public boolean hasNext() {
			return (index >= 0);
		}
		
		public int next() {
			int rv = index;
			index = bits.nextSetBit(index + 1);
			return rv;
		}
		
	}

}
*/