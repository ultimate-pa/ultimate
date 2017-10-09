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

import java.util.EmptyStackException;

/**
 *   Normal stack only has primitive int type
 * */

public class IntStack {

	private int[] mData;
	private int mTopIndex;

	public IntStack() {
		final int INIT_CAPACITY = 30;
		mTopIndex = 0;
		mData = new int[INIT_CAPACITY];
	}

	public IntStack(int initCapacity) {
		if (initCapacity < 0)
			throw new IllegalArgumentException("Negative number " + initCapacity);
		mTopIndex = 0;
		mData = new int[initCapacity];
	}

	public IntStack clone() {
		IntStack result = new IntStack(mData.length);
		for(int i = 0; i < mData.length; i ++) {
			result.mData[i] = mData[i];
		}
		result.mTopIndex = mTopIndex;
		return result;
	}

	public void ensureCapacity(int minCapacity) {
		if (mData.length < minCapacity) {
			int[] copy = new int[minCapacity];
			System.arraycopy(mData, 0, copy, 0, mTopIndex);
			mData = copy;
		}
	}
	
	// --------------- stack interface ------------

	public boolean empty() {
		return (size() == 0);
	}

	public int peek() {
		if (mTopIndex == 0)
			throw new EmptyStackException();
		return mData[mTopIndex - 1];
	}

	public int pop() {
		if (mTopIndex == 0)
			throw new EmptyStackException();
		int item = mData[mTopIndex - 1];
		--mTopIndex;
		return item;
	}

	public void push(int item) {
		if (mTopIndex == mData.length) {
			ensureCapacity((int)(mTopIndex * 1.2) + 1);
		}
		mData[mTopIndex] = item;
		++ mTopIndex;
	}
	
	// -------------------------------------------
    // there may be multiple appearances for each item	
	public boolean contains(int item) {
		return search(item) >= 0;
	}
	
	public IntSet getItems() {
	    IntSet result = UtilIntSet.newIntSet();
	    for(int i = mTopIndex - 1; i >= 0; i --) {
				result.set(mData[i]);
		}
		return result;
	}
	
	// we also can treat it as an array
	public int get(int index) {
		if(index < 0 || index >= mTopIndex)
			throw new RuntimeException("Index out of boundary");
		return mData[index];
	}


	public int capacity() {
		return mData.length;
	}

	public int size() {
		return mTopIndex;
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		if(empty()) return "[]";
		sb.append("[" + mData[0]);
		for(int i = 1; i < mTopIndex; i ++) {
			sb.append("," + mData[i]);
		}
		sb.append("]");
		return sb.toString();
	}
	
	public int search(int item) {
		for(int i = mTopIndex - 1; i >= 0; i --) {
			if(mData[i] == item) return i;
		}
		return -1;
	}
	
	public void clear() {
		mTopIndex = 0;
	}

}
