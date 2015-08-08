/*
 * Copyright (C) 2009-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE Utils Library.
 *
 * The ULTIMATE Utils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Utils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Utils Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Utils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Utils Library grant you additional permission 
 * to convey the resulting work.
 */
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
		return currentElement < powersetSize;
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
