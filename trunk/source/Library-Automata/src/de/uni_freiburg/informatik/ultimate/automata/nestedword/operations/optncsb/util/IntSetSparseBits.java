package util;

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
