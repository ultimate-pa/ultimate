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
		int low,up;
		IntervalNode left,right;
		public IntervalNode(int low,int up) {
			this.low = low;
			this.up = up;
			left = right = null;
		}
	}
	private IntervalNode root;
	/**
	 * Create an allocator for the interval <code>[low,up)</code>
	 * @param low	Lower interval bound (inclusive).
	 * @param up	Upper interval bound (exclusive).
	 */
	public IntAllocator(int low,int up) {
		root = new IntervalNode(low,up);
	}
	public boolean isEmpty() {
		return root == null;
	}
	/**
	 * Allocate the lowest unallocated integer managed by this allocator.
	 * @return Lowest unallocated integer.
	 */
	public int alloc() {
		if (root.low == root.up)
			throw new RuntimeException("Allocation on empty IntAllocator");
		IntervalNode allocNode = root;
		IntervalNode parent = null;
		while (allocNode.left != null) {
			parent = allocNode;
			allocNode = allocNode.left;
		}
		int res = allocNode.low++;
		if (allocNode.low == allocNode.up) {
			if (parent == null)
				// empty allocator
				root = allocNode.right;
			else {
				parent.left = allocNode.right;
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
		int[] res = new int[n];
		for (int i = 0; i < n; ++i)
			res[i] = alloc();
		return res;
	}
	/**
	 * Free one integer.
	 * @param val	Integer to free.
	 */
	public void free(int val) {
		if (root == null) {
			root = new IntervalNode(val,val + 1);
		} else {
			IntervalNode insert = root;
			while (true) {
				if (val + 1 == insert.low) {
					// lower extend
					insert.low = val;
					joinLeft(insert);
					return;
				} else if (val == insert.up) {
					++insert.up;
					joinRight(insert);
					return;
				} else if (val < insert.low) {
					if (insert.left == null) {
						insert.left = new IntervalNode(val,val + 1);
						return;
					}
					insert = insert.left;
				} else {
					if (insert.right == null) {
						insert.right = new IntervalNode(val,val + 1);
						return;
					}
					insert = insert.right;
				}
			}
		}
	}
	/**
	 * Free a sequence of integers.
	 * @param vals Sequence to free.
	 */
	public void free(int[] vals) {
		for (int val : vals)
			free(val);
	}
	private void joinLeft(IntervalNode insert) {
		IntervalNode prev = insert.left;
		IntervalNode parent = insert;
		if (prev == null)
			return;
		while (prev.right != null) {
			parent = prev;
			prev = prev.right;
		}
		if (insert.low == prev.up) {
			insert.low = prev.low;
			// Remove prev
			if (parent == insert)
				parent.left = prev.left;
			else
				parent.right = prev.left;
		}
	}
	private void joinRight(IntervalNode insert) {
		IntervalNode next = insert.right;
		IntervalNode parent = insert;
		if (next == null)
			return;
		while (next.left != null) {
			parent = next;
			next = next.left;
		}
		if (insert.up == next.low) {
			insert.up = next.up;
			// Remove next
			if (parent == insert)
				parent.right = next.right;
			else
				parent.left = next.right;
		}
	}
	/**
	 * Get the highest allocated value.
	 * @return Highest allocated value.
	 */
	public int peekLast() {
		if (root.low == root.up)
			return root.low - 1;
		IntervalNode allocNode = root;
		while (allocNode.right != null)
			allocNode = allocNode.right;
		return allocNode.low - 1;
	}
}
