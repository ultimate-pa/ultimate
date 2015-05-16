package de.uni_freiburg.informatik.ultimate.util;

import java.math.BigInteger;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

/**
 * Returns an Iterator that iterates over the powerset of a given set.
 * @author heizmann@informatik.uni-freiburg.de
 */
public class PowersetIterator<E> implements Iterator<Set<E>> {
	
	private final E[] array;
	private final int powersetSize;
	private int currentElement;
	
	public PowersetIterator(Set<E> set) {
		array = set.toArray((E[]) new Object[set.size()]);
		powersetSize = (int) Math.pow(2, set.size());
		currentElement = 0;
	}
		
	@Override
	public boolean hasNext() {
		return currentElement <= powersetSize;
	}

	@Override
	public Set<E> next() {
		Set<E> result = new HashSet<E>();
		for (int i=0; i<array.length; i++) {
			boolean bitSet = BigInteger.valueOf(currentElement).testBit(i); 
			if (bitSet) {
				result.add(array[i]);
			}
		}
		currentElement++;
		return result;
	}

	@Override
	public void remove() {
		throw new UnsupportedOperationException("modification not supported");
	}

}
