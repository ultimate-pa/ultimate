package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.Minimizer;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.MinimizerStep;

/**
 * A divide and conquer minimizer inspired similar to merge sort or binary search. Recursively splits the input in two
 * halfs and tries to delete the individually.
 *
 * <ul>
 * <li>To be similar to ddmin the empty set (i.e. deletion of the full input) is not considered a a valid variant.
 * <li>The algorithm removes elements in strict order, i.e. the first half always completely minimized before second
 * half is even look at. Depending on the structure of dependencies in the input this can be good or bad. It also means
 * that the result's size decreases slower than ddmin.
 * <li>The result is not minimal but all variants are unique.
 * </ul>
 *
 * Elements can either be removed front to back, i.e. for any two elements at indices i < j, the element at index i is
 * removed before j, or the other way around. This option can have a significant impact if dependencies in a certain
 * direction are more likely.
 */
public class BinarySearchMinimizer implements Minimizer {
	final class BinarySearchStep<E> implements MinimizerStep<E> {
		final List<E> result;
		final List<E> variant;
		final ImmutableStack<Part> stack;
		final int delta;

		BinarySearchStep(final List<E> result, final List<E> variant, final ImmutableStack<Part> stack,
				final int delta) {
			this.result = result;
			this.variant = variant;
			this.stack = stack;
			this.delta = delta;
		}

		@Override
		public List<E> getResult() {
			return result;
		}

		@Override
		public List<E> getVariant() {
			return variant;
		}

		@Override
		public boolean isDone() {
			return false;
		}

		@Override
		public MinimizerStep<E> next(final boolean keepVariant) {
			return keepVariant ? reduceToCurrentVariant() : tryNextVariant();
		}

		MinimizerStep<E> reduceToCurrentVariant() {
			final Part part = this.stack.peek();
			ImmutableStack<Part> nextStack = this.stack.pop();
			if (part.isFirstHalf) {
				// Immediately split the first half, because removing the left
				// and right half together has been tested in the last step,
				// which
				// was not successful (if it was, there would have been no split
				// resulting in these two halfs)
				nextStack = split(nextStack);
			}
			return createNextStep(variant, nextStack, iterateFrontToBack ? delta - part.size() : delta);
		}

		MinimizerStep<E> tryNextVariant() {
			return createNextStep(result, split(stack), delta);
		}
	}

	static class Part {
		final int begin;
		final int end;
		final boolean isFirstHalf;

		public Part(final int begin, final int end, final boolean isFirstHalf) {
			this.begin = begin;
			this.end = end;
			this.isFirstHalf = isFirstHalf;
		}

		int size() {
			return end - begin;
		}
	}

	private final boolean iterateFrontToBack;

	/**
	 * @param iterateFrontToBack
	 *            remove elements at front first
	 */
	public BinarySearchMinimizer(final boolean iterateFrontToBack) {
		this.iterateFrontToBack = iterateFrontToBack;
	}

	@Override
	public <E> MinimizerStep<E> create(final List<E> input) {
		return createNextStep(input, split(ImmutableStack.of(new Part(0, input.size(), false))), 0);
	}

	private <E> MinimizerStep<E> createNextStep(final List<E> result, final ImmutableStack<Part> stack,
			final int delta) {
		final int size = result.size();
		if (size < 2 || stack.empty()) {
			return new FinalMinimizerStep<>(result);
		}

		final Part part = stack.peek();
		final List<E> variant = MinimizerListOps.subListComplement(result, part.begin + delta, part.end + delta);
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
		final int size = part.end - part.begin;
		ImmutableStack<Part> nextStack = stack.pop();
		if (size >= 2) {
			final int mid = size >>> 1;
			final Part left = new Part(part.begin, part.begin + mid, iterateFrontToBack);
			final Part right = new Part(part.begin + mid, part.end, !iterateFrontToBack);
			nextStack = iterateFrontToBack ? nextStack.push(right).push(left) : nextStack.push(left).push(right);
		}
		return nextStack;
	}
}