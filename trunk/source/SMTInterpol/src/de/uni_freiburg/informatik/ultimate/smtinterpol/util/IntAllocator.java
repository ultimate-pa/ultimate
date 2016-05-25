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
package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

/**
 * An allocator for integers.  It allocates integers from a given interval with
 * the guarantee that you always get the lowest not-allocated integer.
 * 
 * You might increase the interval by freeing a value which has previously not
 * been part of the allocation interval, but you should never double free the
 * same integer without allocating it in between.
 * @author Juergen Christ
 */
public class IntAllocator {
	private static class IntervalNode {
		int mLow,mUp;
		IntervalNode mLeft,mRight;
		public IntervalNode(int low,int up) {
			mLow = low;
			mUp = up;
			mLeft = mRight = null;
		}
	}
	private IntervalNode mRoot;
	/**
	 * Create an allocator for the interval <code>[low,up)</code>
	 * @param low	Lower interval bound (inclusive).
	 * @param up	Upper interval bound (exclusive).
	 */
	public IntAllocator(int low,int up) {
		mRoot = new IntervalNode(low,up);
	}
	public boolean isEmpty() {
		return mRoot == null;
	}
	/**
	 * Allocate the lowest unallocated integer managed by this allocator.
	 * @return Lowest unallocated integer.
	 */
	public int alloc() {
		if (mRoot.mLow == mRoot.mUp) {
			throw new RuntimeException("Allocation on empty IntAllocator");
		}
		IntervalNode allocNode = mRoot;
		IntervalNode parent = null;
		while (allocNode.mLeft != null) {
			parent = allocNode;
			allocNode = allocNode.mLeft;
		}
		final int res = allocNode.mLow++;
		if (allocNode.mLow == allocNode.mUp) {
			if (parent == null) {
				// empty allocator
				mRoot = allocNode.mRight;
			} else {
				parent.mLeft = allocNode.mRight;
			}
		}
		return res;
	}
	/**
	 * Allocate a sequence of integer.
	 * @param n Number of integers to allocate.
	 * @return Allocated integers.
	 */
	public int[] alloc(int n) {
		final int[] res = new int[n];
		for (int i = 0; i < n; ++i) {
			res[i] = alloc();
		}
		return res;
	}
	/**
	 * Free one integer.
	 * @param val	Integer to free.
	 */
	public void free(int val) {
		if (mRoot == null) {
			mRoot = new IntervalNode(val,val + 1);
		} else {
			IntervalNode insert = mRoot;
			while (true) {
				if (val + 1 == insert.mLow) {
					// lower extend
					insert.mLow = val;
					joinLeft(insert);
					return;
				} else if (val == insert.mUp) {
					++insert.mUp;
					joinRight(insert);
					return;
				} else if (val < insert.mLow) {
					if (insert.mLeft == null) {
						insert.mLeft = new IntervalNode(val,val + 1);
						return;
					}
					insert = insert.mLeft;
				} else {
					if (insert.mRight == null) {
						insert.mRight = new IntervalNode(val,val + 1);
						return;
					}
					insert = insert.mRight;
				}
			}
		}
	}
	/**
	 * Free a sequence of integers.
	 * @param vals Sequence to free.
	 */
	public void free(int[] vals) {
		for (final int val : vals) {
			free(val);
		}
	}
	private void joinLeft(IntervalNode insert) {
		IntervalNode prev = insert.mLeft;
		if (prev == null) {
			return;
		}
		IntervalNode parent = insert;
		while (prev.mRight != null) {
			parent = prev;
			prev = prev.mRight;
		}
		if (insert.mLow == prev.mUp) {
			insert.mLow = prev.mLow;
			// Remove prev
			if (parent == insert) {
				parent.mLeft = prev.mLeft;
			} else {
				parent.mRight = prev.mLeft;
			}
		}
	}
	private void joinRight(IntervalNode insert) {
		IntervalNode next = insert.mRight;
		if (next == null) {
			return;
		}
		IntervalNode parent = insert;
		while (next.mLeft != null) {
			parent = next;
			next = next.mLeft;
		}
		if (insert.mUp == next.mLow) {
			insert.mUp = next.mUp;
			// Remove next
			if (parent == insert) {
				parent.mRight = next.mRight;
			} else {
				parent.mLeft = next.mRight;
			}
		}
	}
	/**
	 * Get the highest allocated value.
	 * @return Highest allocated value.
	 */
	public int peekLast() {
		if (mRoot.mLow == mRoot.mUp) {
			return mRoot.mLow - 1;
		}
		IntervalNode allocNode = mRoot;
		while (allocNode.mRight != null) {
			allocNode = allocNode.mRight;
		}
		return allocNode.mLow - 1;
	}
}
