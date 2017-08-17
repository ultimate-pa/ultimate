package util;

import gnu.trove.iterator.TIntIterator;
import gnu.trove.set.TIntSet;
import gnu.trove.set.hash.TIntHashSet;

public class IntSetTIntSet implements IntSet {
	
	private final TIntSet set;
	
	public IntSetTIntSet() {
		set = new TIntHashSet();
	}

	@Override
	public IntIterator iterator() {
		return new TIntSetIterator(this);
	}

	@Override
	public IntSet clone() {
		IntSetTIntSet copy = new IntSetTIntSet();
		copy.set.addAll(set);
		return copy;
	}

	@Override
	public void andNot(IntSet set) {
		if(! (set instanceof IntSetTIntSet)) {
			System.err.println("OPERAND should be TIntSet");
			System.exit(-1);
		}
		IntSetTIntSet temp = (IntSetTIntSet)set;
		this.set.removeAll(temp.set);
	}

	@Override
	public void and(IntSet set) {
		if(! (set instanceof IntSetTIntSet)) {
			System.err.println("OPERAND should be TIntSet");
			System.exit(-1);
		}
		IntSetTIntSet temp = (IntSetTIntSet)set;
		this.set.retainAll(temp.set);
	}

	@Override
	public void or(IntSet set) {
		if(! (set instanceof IntSetTIntSet)) {
			System.err.println("OPERAND should be TIntSet");
			System.exit(-1);
		}
		IntSetTIntSet temp = (IntSetTIntSet)set;
		this.set.addAll(temp.set);
	}

	@Override
	public boolean get(int value) {
		return set.contains(value);
	}
	
	@Override
	public void set(int value) {
		set.add(value);
	}

	@Override
	public void clear(int value) {
		set.remove(value);
	}
	
	@Override
	public void clear() {
		set.clear();
	}
	
	@Override
	public String toString() {
		return set.toString();
	}

	@Override
	public boolean isEmpty() {
		return set.isEmpty();
	}

	@Override
	public int cardinality() {
		return set.size();
	}

	@Override
	public boolean subsetOf(IntSet set) {
		if(! (set instanceof IntSetTIntSet)) {
			System.err.println("OPERAND should be TIntSet");
			System.exit(-1);
		}
		IntSetTIntSet temp = (IntSetTIntSet)set;
		return temp.set.containsAll(this.set);
	}

	@Override
	public boolean contentEq(IntSet set) {
		if(! (set instanceof IntSetTIntSet)) {
			System.err.println("OPERAND should be TIntSet");
			System.exit(-1);
		}
		IntSetTIntSet temp = (IntSetTIntSet)set;
		return this.set.equals(temp.set);
	}

	@Override
	public Object get() {
		return set;
	}
	
	public boolean equals(Object obj) {
		if(! (obj instanceof IntSetTIntSet)) {
			System.err.println("OPERAND should be TIntSet");
			System.exit(-1);
		}
		IntSetTIntSet temp = (IntSetTIntSet)obj;
		return this.contentEq(temp);
	}
	
	public static class TIntSetIterator implements IntIterator {

		private TIntIterator setIter;
		
		public TIntSetIterator(IntSetTIntSet set) {
			setIter = set.set.iterator();
		}
		
		public boolean hasNext() {
			return setIter.hasNext();
		}
		
		public int next() {
			return setIter.next();
		}
		
	}

}
