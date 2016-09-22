/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.util;

import java.util.Arrays;

/**
 * This can be helpful for constructing an exponential number of elements
 * @author Matthias Heizmann
 *
 */
public class LexicographicCounter {

	private final int[] mNumberOfValues;
	private final int[] mCounter;
	private final int mNumberOfValuesProduct;

	public LexicographicCounter(final int[] numberOfValues) {
		super();
		mNumberOfValues = numberOfValues;
		mNumberOfValuesProduct = Arrays.stream(mNumberOfValues).reduce(0, (x,y) -> x*y);
		mCounter = new int[mNumberOfValues.length];
	}
	
	public int[] getCurrentValue() {
		return mCounter;
	}
	
	public void increment() {
		for (int i=0; true; i++) {
			mCounter[i]++;
			if(mCounter[i] < mNumberOfValues[i]) {
				return;
			} else {
				mCounter[i] = 0;
			}
		}
	}
	
	public boolean isZero() {
		return Arrays.stream(mCounter).allMatch(x -> x == 0);
	}

	/**
	 * @return the numberOfValuesProduct
	 */
	public int getNumberOfValuesProduct() {
		return mNumberOfValuesProduct;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "Current value=" + Arrays.toString(mCounter) + ", mNumberOfValues="
				+ Arrays.toString(mNumberOfValues);
	}
	
	
	
	
}
