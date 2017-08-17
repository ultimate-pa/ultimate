package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util;

import java.util.Iterator;

class PowerSetEmpty implements Iterator<IntSet> {
	
	private boolean hasNext;
	
	public PowerSetEmpty() {
		hasNext = true;
	}

	@Override
	public boolean hasNext() {
		return hasNext;
	}

	@Override
	public IntSet next() {
		assert hasNext();
		hasNext = false;
		return UtilIntSet.newIntSet();
	}

}
