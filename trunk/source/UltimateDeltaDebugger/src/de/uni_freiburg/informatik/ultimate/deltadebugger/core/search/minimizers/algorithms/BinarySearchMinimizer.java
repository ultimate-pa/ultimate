/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IMinimizer;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IMinimizerStep;

/**
 * A divide and conquer minimizer similar to merge sort or binary search. Recursively splits the input in two halfs and
 * tries to minimize each one individually.
 *
 * <ul>
 * <li>Similar to ddmin the empty set (i.e. deletion of the full input) is not considered a a valid variant.
 * <li>The algorithm removes elements in strict order, i.e. the first half always completely minimized before second
 * half is even looked at. Depending on the structure of dependencies in the input this can be good or bad. It also
 * means that the result's size can decrease slower than ddmin if large parts in a second half can be removed.
 * <li>The result is not minimal but all variants are unique.
 * </ul>
 *
 * Elements can either be removed front to back, i.e. for any two elements at indices i < j, the element at index i is
 * removed before j, or the other way around. This option can have a significant impact if dependencies in a certain
 * direction are more likely.
 */
public class BinarySearchMinimizer implements IMinimizer {
	private final boolean mIterateFrontToBack;
	private final int mSplitSizeLimit;

	/**
	 * @param iterateFrontToBack
	 *            Remove elements at front first.
	 */
	public BinarySearchMinimizer(final boolean iterateFrontToBack) {
		mIterateFrontToBack = iterateFrontToBack;
		mSplitSizeLimit = 2;
	}

	/**
	 * @param iterateFrontToBack
	 *            Remove elements at front first.
	 * @param splitSizeLimit
	 *            Minimum subset size that is split in two halfs.
	 */
	public BinarySearchMinimizer(final boolean iterateFrontToBack, final int splitSizeLimit) {
		mIterateFrontToBack = iterateFrontToBack;
		mSplitSizeLimit = Math.max(2, splitSizeLimit);
	}

	@Override
	public <E> IMinimizerStep<E> create(final List<E> input) {
		return createNextStep(input, split(ImmutableStack.of(new Part(0, input.size(), false))), 0);
	}

	private <E> IMinimizerStep<E> createNextStep(final List<E> result, final ImmutableStack<Part> stack,
			final int delta) {
		final int size = result.size();
		if (size < 2 || stack.isEmpty()) {
			return new FinalMinimizerStep<>(result);
		}

		final Part part = stack.peek();
		final List<E> variant = MinimizerListOps.subListComplement(result, part.mBegin + delta, part.mEnd + delta);
		return new BinarySearchStep<>(result, variant, stack, delta);
	}

	@Override
	public boolean isEachVariantUnique() {
		return true;
	}

	@Override
	public boolean isResultMinimal() {
		return false;
	}

	ImmutableStack<Part> split(final ImmutableStack<Part> stack) {
		final Part part = stack.peek();
		final int size = part.mEnd - part.mBegin;
		ImmutableStack<Part> nextStack = stack.pop();
		if (size >= mSplitSizeLimit) {
			final int mid = size >>> 1;
			final Part left = new Part(part.mBegin, part.mBegin + mid, mIterateFrontToBack);
			final Part right = new Part(part.mBegin + mid, part.mEnd, !mIterateFrontToBack);
			nextStack = mIterateFrontToBack ? nextStack.push(right).push(left) : nextStack.push(left).push(right);
		}
		return nextStack;
	}

	/**
	 * A binary search step.
	 *
	 * @param <E>
	 *            element type
	 */
	final class BinarySearchStep<E> implements IMinimizerStep<E> {
		private final List<E> mResult;
		private final List<E> mVariant;
		private final ImmutableStack<Part> mStack;
		private final int mDelta;

		BinarySearchStep(final List<E> result, final List<E> variant, final ImmutableStack<Part> stack,
				final int delta) {
			mResult = result;
			mVariant = variant;
			mStack = stack;
			mDelta = delta;
		}

		@Override
		public List<E> getResult() {
			return mResult;
		}

		@Override
		public List<E> getVariant() {
			return mVariant;
		}

		@Override
		public boolean isDone() {
			return false;
		}

		@Override
		public IMinimizerStep<E> next(final boolean keepVariant) {
			return keepVariant ? reduceToCurrentVariant() : tryNextVariant();
		}

		IMinimizerStep<E> reduceToCurrentVariant() {
			final Part part = this.mStack.peek();
			ImmutableStack<Part> nextStack = this.mStack.pop();
			if (part.mIsFirstHalf) {
				// Immediately split the first half, because removing the left and right half together has been tested
				// in the last step, which was not successful (if it was, there would have been no split
				// resulting in these two halfs)
				nextStack = split(nextStack);
			}
			return createNextStep(mVariant, nextStack, mIterateFrontToBack ? (mDelta - part.size()) : mDelta);
		}

		IMinimizerStep<E> tryNextVariant() {
			return createNextStep(mResult, split(mStack), mDelta);
		}
	}

	/**
	 * A part in the binary search.
	 */
	static class Part {
		private final int mBegin;
		private final int mEnd;
		private final boolean mIsFirstHalf;

		public Part(final int begin, final int end, final boolean isFirstHalf) {
			mBegin = begin;
			mEnd = end;
			mIsFirstHalf = isFirstHalf;
		}

		int size() {
			return mEnd - mBegin;
		}
	}
}
