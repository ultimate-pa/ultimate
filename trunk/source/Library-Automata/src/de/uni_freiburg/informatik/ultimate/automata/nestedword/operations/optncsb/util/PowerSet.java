package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util;

import java.util.Iterator;

public class PowerSet implements Iterator<IntSet> {
	
	private Iterator<IntSet> iterator;
	public PowerSet(IntSet set) {
		if(set.isEmpty()) {
			iterator = new PowerSetEmpty();
		}else {
			iterator = new PowerSetPositive(set);
		}
	}

	@Override
	public boolean hasNext() {
		return iterator.hasNext();
	}

	@Override
	public IntSet next() {
		assert hasNext();
		return iterator.next();
	}
	
	
	public static void main(String[] args) {
		IntSetBits bits = new IntSetBits();
		bits.set(2);
		bits.set(3);
		bits.set(6);
//		bits.set(7);
		bits.set(9);
		System.out.println(bits);
		PowerSet ps = new PowerSet(bits);
		int i = 0;
		while(ps.hasNext()) {
			IntSet subset = ps.next();
			i ++;
			System.out.println(" " + subset);
		}
		System.out.println("number "+ i);
		
		
		bits.clear();
		System.out.println(bits);
		ps = new PowerSet(bits);
		i = 0;
		while(ps.hasNext()) {
			IntSet subset = ps.next();
			i ++;
			System.out.println(" " + subset);
		}
		System.out.println("number "+ i);
	}

}
