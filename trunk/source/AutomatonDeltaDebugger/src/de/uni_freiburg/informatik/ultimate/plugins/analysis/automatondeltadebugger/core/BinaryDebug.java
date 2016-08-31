/*
 * Copyright (C) 2015-2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automaton Delta Debugger.
 * 
 * The ULTIMATE Automaton Delta Debugger is free software: you can redistribute
 * it and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * The ULTIMATE Automaton Delta Debugger is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automaton Delta Debugger. If not, see
 * <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automaton Delta Debugger, or any covered work, by linking or
 * combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automaton Delta Debugger grant you additional
 * permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core;

import java.util.ArrayDeque;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.AShrinker;

/**
 * Reduces a list of objects in a binary search manner until a local minimum is
 * found.
 * Note that the local minimum is only according to the current shrinker, i.e.,
 * the respective shrinker cannot be applied to a subinterval of objects anymore
 * while still producing the error. However, removing, say, objects 1 and 3
 * might still work.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <T>
 *            shrinker data structure
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class BinaryDebug<T, LETTER, STATE> extends ADebug<T, LETTER, STATE> {
	/**
	 * Left and right bound for the list of objects.
	 */
	private static class SublistBounds {
		private final int mLeft;
		private final int mRight;
		private final boolean mIsLhs;
		
		SublistBounds(final int left, final int right, final boolean isLhs) {
			this.mLeft = left;
			this.mRight = right;
			this.mIsLhs = isLhs;
		}
		
		@Override
		public String toString() {
			final StringBuilder b = new StringBuilder();
			b.append("(");
			b.append(mLeft);
			b.append(", ");
			b.append(mRight);
			b.append(")");
			if (mIsLhs) {
				b.append("*");
			}
			return b.toString();
		}
	}
	
	private final ArrayDeque<SublistBounds> mStack;
	private SublistBounds mSublistBounds;
	
	/**
	 * Constructor.
	 * 
	 * @param tester
	 *            tester
	 * @param shrinker
	 *            shrinker
	 */
	public BinaryDebug(final ATester<LETTER, STATE> tester,
			final AShrinker<T, LETTER, STATE> shrinker) {
		super(tester, shrinker);
		mStack = new ArrayDeque<>();
		mSublistBounds = null;
	}
	
	/**
	 * Splits a list into two sublists of equal size.
	 * 
	 * @param bounds
	 *            bounds
	 */
	private void split(final SublistBounds bounds) {
		final int left = bounds.mLeft;
		final int right = bounds.mRight;
		
		// do not split intervals of size <= 1 (useless and would run forever)
		if (right - left <= 1) {
			return;
		}
		
		final int mid = (left + right) / 2;
		final boolean isLhs;
		if (mid < right) {
			mStack.push(new SublistBounds(mid, right, false));
			isLhs = true;
		} else {
			isLhs = false;
		}
		if (left < mid) {
			mStack.push(new SublistBounds(left, mid, isLhs));
		}
	}
	
	@Override
	public boolean run() {
		boolean result = false;
		final List<T> list = mShrinker.extractList();
		if (list.isEmpty()) {
			return result;
		}
		mStack.add(new SublistBounds(0, list.size(), false));
		while (!mStack.isEmpty()) {
			mSublistBounds = mStack.poll();
			final List<T> sublist =
					list.subList(mSublistBounds.mLeft, mSublistBounds.mRight);
			if (sublist.isEmpty()) {
				continue;
			}
			
			// run test
			result |= super.test(sublist);
		}
		return result;
	}
	
	@Override
	protected void errorAction() {
		/*
		 * When the success happened on the first half part, we can remove the
		 * corresponding second half part and directly work on its children.
		 * This is because by removing the second half part we would have
		 * removed the whole sublist, and this was, by construction, already
		 * unsuccessful in a previous test.
		 */
		if (mSublistBounds.mIsLhs) {
			split(mStack.poll());
		}
	}
	
	@Override
	protected void noErrorAction() {
		split(mSublistBounds);
	}
}
