package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util;

import java.util.Iterator;
import java.util.TreeSet;


public class IntSetTreeSet implements IntSet {
	
	private final TreeSet<Integer> set;
	
	public IntSetTreeSet() {
		set = new TreeSet<>();
	}

	@Override
	public IntIterator iterator() {
		return new TreeSetIterator(this);
	}

	@Override
	public IntSet clone() {
		IntSetTreeSet copy = new IntSetTreeSet();
		copy.set.addAll(set);
		return copy;
	}

	@Override
	public void andNot(IntSet set) {
		if(! (set instanceof IntSetTreeSet)) {
			System.err.println("OPERAND should be TreeSet");
			System.exit(-1);
		}
		IntSetTreeSet temp = (IntSetTreeSet)set;
		this.set.removeAll(temp.set);
	}

	@Override
	public void and(IntSet set) {
		if(! (set instanceof IntSetTreeSet)) {
			System.err.println("OPERAND should be TreeSet");
			System.exit(-1);
		}
		IntSetTreeSet temp = (IntSetTreeSet)set;
		this.set.retainAll(temp.set);
	}

	@Override
	public void or(IntSet set) {
		if(! (set instanceof IntSetTreeSet)) {
			System.err.println("OPERAND should be TreeSet");
			System.exit(-1);
		}
		IntSetTreeSet temp = (IntSetTreeSet)set;
		this.set.addAll(temp.set);
	}

	@Override
	public boolean get(int value) {
		return set.contains(value);
	}

	@Override
	public void clear(int value) {
		set.remove(value);
	}
	
	@Override
	public String toString() {
		return set.toString();
	}
	
	@Override
	public void clear() {
		set.clear();
	}
	
	@Override
	public void set(int value) {
		set.add(value);
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
		if(! (set instanceof IntSetTreeSet)) {
			System.err.println("OPERAND should be TreeSet");
			System.exit(-1);
		}
		IntSetTreeSet temp = (IntSetTreeSet)set;
		return temp.set.containsAll(this.set);
	}

	@Override
	public boolean contentEq(IntSet set) {
		if(! (set instanceof IntSetTreeSet)) {
			System.err.println("OPERAND should be TreeSet");
			System.exit(-1);
		}
		IntSetTreeSet temp = (IntSetTreeSet)set;
		return this.set.equals(temp.set);
	}

	@Override
	public Object get() {
		return set;
	}
	
	public boolean equals(Object obj) {
		if(! (obj instanceof IntSetTreeSet)) {
			System.err.println("OPERAND should be TreeSet");
			System.exit(-1);
		}
		IntSetTreeSet temp = (IntSetTreeSet)obj;
		return this.contentEq(temp);
	}
	
	public static class TreeSetIterator implements IntIterator {

		private Iterator<Integer> iterator;
		
		public TreeSetIterator(IntSetTreeSet set) {
			this.iterator = set.set.iterator();
		}
		
		public boolean hasNext() {
			return iterator.hasNext();
		}
		
		public int next() {
			return iterator.next();
		}
		
	}
	

}
