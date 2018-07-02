/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Util Library.
 * 
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Util Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

/**
 * Returns an Iterator that iterates over the powerset of a given set.
 * @author heizmann@informatik.uni-freiburg.de
 */
public class PowersetIterator<E> implements Iterator<Set<E>> {
	
	private final List<E> mList;
	private final int mPowersetSize;
	private int mCurrentElement;
	
	public PowersetIterator(Set<E> set) {
		mList = new ArrayList<E>(set);
		mPowersetSize = (int) Math.pow(2, set.size());
		mCurrentElement = 0;
	}
	
	/**
	 * Warning behavior undefined if list does not represent a set (i.e., list
	 * contains elements twice).
	 */
	public PowersetIterator(List<E> setAsList) {
		mList = setAsList;
		mPowersetSize = (int) Math.pow(2, setAsList.size());
		mCurrentElement = 0;
	}
		
	@Override
	public boolean hasNext() {
		return mCurrentElement < mPowersetSize;
	}

	@Override
	public Set<E> next() {
		final Set<E> result = new HashSet<E>();
		for (int i=0; i<mList.size(); i++) {
			final boolean bitSet = BigInteger.valueOf(mCurrentElement).testBit(i); 
			if (bitSet) {
				result.add(mList.get(i));
			}
		}
		mCurrentElement++;
		return result;
	}

	@Override
	public void remove() {
		throw new UnsupportedOperationException("modification not supported");
	}

}
