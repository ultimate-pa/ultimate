package util;

import java.util.BitSet;

public class IntSetBits implements IntSet {
	
	private BitSet set;
	
	public IntSetBits() {
		set = new BitSet();
	}

	@Override
	public IntIterator iterator() {
		return new SparseBitsIterator(this);
	}

	@Override
	public IntSet clone() {
		IntSetBits bits = new IntSetBits();
		bits.set = (BitSet) set.clone();
		return bits;
	}

	@Override
	public void andNot(IntSet set) {
		if(! (set instanceof IntSetBits)) {
			System.err.println("OPERAND should be BitSet");
			System.exit(-1);
		}
		BitSet bits = (BitSet) set.get();
		this.set.andNot(bits);
	}

	@Override
	public void and(IntSet set) {
		if(! (set instanceof IntSetBits)) {
			System.err.println("OPERAND should be BitSet");
			System.exit(-1);
		}
		BitSet bits = (BitSet) set.get();
		this.set.and(bits);
	}

	@Override
	public void or(IntSet set) {
		if(! (set instanceof IntSetBits)) {
			System.err.println("OPERAND should be BitSet");
			System.exit(-1);
		}
		BitSet bits = (BitSet) set.get();
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
		if(! (set instanceof IntSetBits)) {
			System.err.println("OPERAND should be BitSet");
			System.exit(-1);
		}
		IntSetBits temp = (IntSetBits) set;
		return temp.set.intersects(this.set);
	}
	

	@Override
	public boolean subsetOf(IntSet set) {
		if(! (set instanceof IntSetBits)) {
			System.err.println("OPERAND should be BitSet");
			System.exit(-1);
		}
		BitSet temp = (BitSet) this.set.clone();
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
		return this.set.equals(bits);
	}

	@Override
	public Object get() {
		return set;
	}
	
	@Override
	public String toString() {
		return set.toString();
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

		private BitSet bits;
		private int index;
		
		public SparseBitsIterator(IntSetBits set) {
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
