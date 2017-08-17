package util;

import java.util.HashSet;
import java.util.Iterator;


public class IntSetHashSet implements IntSet {
	
	private final HashSet<Integer> set;
	
	public IntSetHashSet() {
		set = new HashSet<>();
	}

	@Override
	public IntIterator iterator() {
		return new HashSetIterator(this);
	}

	@Override
	public IntSet clone() {
		IntSetHashSet copy = new IntSetHashSet();
		copy.set.addAll(set);
		return copy;
	}

	@Override
	public void andNot(IntSet set) {
		if(! (set instanceof IntSetHashSet)) {
			System.err.println("OPERAND should be HashSet");
			System.exit(-1);
		}
		IntSetHashSet temp = (IntSetHashSet)set;
		this.set.removeAll(temp.set);
	}

	@Override
	public void and(IntSet set) {
		if(! (set instanceof IntSetHashSet)) {
			System.err.println("OPERAND should be HashSet");
			System.exit(-1);
		}
		IntSetHashSet temp = (IntSetHashSet)set;
		this.set.retainAll(temp.set);
	}

	@Override
	public void or(IntSet set) {
		if(! (set instanceof IntSetHashSet)) {
			System.err.println("OPERAND should be HashSet");
			System.exit(-1);
		}
		IntSetHashSet temp = (IntSetHashSet)set;
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
		if(! (set instanceof IntSetHashSet)) {
			System.err.println("OPERAND should be HashSet");
			System.exit(-1);
		}
		IntSetHashSet temp = (IntSetHashSet)set;
		return temp.set.containsAll(this.set);
	}

	@Override
	public boolean contentEq(IntSet set) {
		if(! (set instanceof IntSetHashSet)) {
			System.err.println("OPERAND should be HashSet");
			System.exit(-1);
		}
		IntSetHashSet temp = (IntSetHashSet)set;
		return this.set.equals(temp.set);
	}

	@Override
	public Object get() {
		return set;
	}
	
	public boolean equals(Object obj) {
		if(! (obj instanceof IntSetHashSet)) {
			System.err.println("OPERAND should be HashSet");
			System.exit(-1);
		}
		IntSetHashSet temp = (IntSetHashSet)obj;
		return this.contentEq(temp);
	}
	
	public static class HashSetIterator implements IntIterator {

		private Iterator<Integer> setIter;
		
		public HashSetIterator(IntSetHashSet set) {
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
