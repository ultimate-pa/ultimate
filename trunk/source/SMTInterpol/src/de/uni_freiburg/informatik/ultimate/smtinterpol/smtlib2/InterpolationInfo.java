/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

import de.uni_freiburg.informatik.ultimate.logic.Term;

public class InterpolationInfo {
	Term[] mPartitions;
	int[] mStartOfSubTrees;
	int   mSize = 0;
	boolean mIsAndTerm = false;
	
	public InterpolationInfo() {
		mPartitions = new Term[5];
		mStartOfSubTrees = new int[5];
	}
	
	private void grow(int minsize) {
		int newsize = 2 * mPartitions.length;
		if (newsize < minsize) {
			newsize = minsize + 1;
		}
		final Term[] newPartitions = new Term[newsize];
		final int[] newStartOfSubTrees = new int[newsize];
		System.arraycopy(mPartitions, 0, newPartitions, 0, mSize);
		System.arraycopy(mStartOfSubTrees, 0, newStartOfSubTrees, 0, mSize);
		mPartitions = newPartitions;
		mStartOfSubTrees = newStartOfSubTrees;
	}
	
	public void makeAndTerm() {
		mIsAndTerm = true;
	}
	
	public void addParent(Term partition) {
		if (mSize + 1 >= mPartitions.length) {
			grow(mSize + 1);
		}
		mPartitions[mSize] = partition;
		mStartOfSubTrees[mSize] = 0;
		mSize++;
	}
	
	public void addSibling(InterpolationInfo sibling) {
		if (mSize + sibling.mSize >= mPartitions.length) {
			grow(mSize + sibling.mSize);
		}
		System.arraycopy(sibling.mPartitions, 0, mPartitions, mSize, sibling.mSize);
		for (int i = 0; i < sibling.mSize; i++) {
			mStartOfSubTrees[mSize + i] = mSize + sibling.mStartOfSubTrees[i];
		}
		mSize += sibling.mSize;
	}
	
	public Term[] getPartition() {
		if (mPartitions.length != mSize) {
			final Term[] newPartitions = new Term[mSize];
			System.arraycopy(mPartitions, 0, newPartitions, 0, mSize);
			return newPartitions;
		}
		return mPartitions;
	}

	public int[] getTreeStructure() {
		if (mStartOfSubTrees.length != mSize) {
			final int[] newStartOfSubtrees = new int[mSize];
			System.arraycopy(mStartOfSubTrees, 0, newStartOfSubtrees, 0, mSize);
			return newStartOfSubtrees;
		}
		return mStartOfSubTrees;
	}
	
	public boolean isEmpty() {
		return mSize == 0;
	}

	public boolean isAndTerm() {
		return mIsAndTerm;
	}
	
	public boolean isClosedTree() {
		return !mIsAndTerm && mSize > 0 && mStartOfSubTrees[mSize - 1] == 0;
	}
}
