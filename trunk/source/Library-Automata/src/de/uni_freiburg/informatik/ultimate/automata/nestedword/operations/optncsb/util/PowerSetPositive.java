/*
 * Copyright (C) 2017 Yong Li (liyong@ios.ac.cn)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util;

import java.util.Iterator;

/**
 * @author Yong Li (liyong@ios.ac.cn)
 * */

class PowerSetPositive implements Iterator<IntSet> {

	private Valuation mValuation;
	
	private final IntSet mSet;
	private final int[] mIntArr;
	
	public PowerSetPositive(IntSet set) {
		assert ! set.isEmpty();
		this.mSet = set;
		mIntArr = new int[mSet.cardinality()];
		int index = 0;
		IntIterator iter = mSet.iterator();
		while(iter.hasNext()) {
			mIntArr[index ++] = iter.next();
		}
		this.mValuation = new Valuation(mSet.cardinality());
	}

	@Override
	public boolean hasNext() {
		int index = mValuation.nextSetBit(0); // whether we have got out of the array
		return index < mValuation.size();
	}

	@Override
	public IntSet next() {
		assert hasNext();
		Valuation val = mValuation.clone();
		mValuation.increment();
		IntSet bits = UtilIntSet.newIntSet();
		for(int n = val.nextSetBit(0); n >= 0 ; n = val.nextSetBit(n + 1)) {
			bits.set(mIntArr[n]);
		}
		return bits;
	}

}
