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

import java.util.EnumSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IMinimizer;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IMinimizerStep;

/**
 * Minimizer based on the original ddmin algorithm. Several options have been added to adjust the order and overall
 * amount generated test inputs.
 * <ul>
 * <li>The empty set is not considered a valid test input by ddmin and hence not returned by this minimizer.
 * <li>In contrast to the original algorithm subsets are removed back to front by default.
 * </ul>
 */
public class DDMinMinimizer implements IMinimizer {
	/**
	 * Options.
	 */
	public enum Option {
		/**
		 * In the original ddmin definition complements of subsets are checked in the same order as the corresponding
		 * subsets. This implementation checks complements in reverse order, i.e. subsets are iterated back to front in
		 * order to remove elements at the back first. This small difference is useful if elements are more likely to
		 * depend on preceding elements than the other way around. This flag disables this heuristic and gives the
		 * original ddmin algorithm from the paper. Motivation: In a C source a declaration comes before any reference,
		 * so removing elements from front to back is more likely to cause compilations errors because declarations are
		 * removed before their references.
		 */
		STRICT_COMPLEMENT_ORDER,
		
		/**
		 * Do not test single subsets, only complements thereof. The resulting algorithm is similar to a binary search
		 * but with a queue instead of a stack, i.e. the removal of larger subsets is always tested before smaller
		 * subsets and the size of test inputs may decrease faster. Motivation: Reduction to a single subset at higher
		 * granularities may be unlikely to succeed for certain inputs (but is repeated after each successful reduction
		 * to a complement). Skipping this iteration improves worst case performance and is still one-minimal.
		 */
		SKIP_SUBSET_TESTS,
		
		/**
		 * Immediately start at max granularity.
		 */
		SKIP_TO_MAX_GRANULARITY,
		
		/**
		 * Do not restart after successfully reducing to a complement.
		 */
		CONTINUE_AFTER_REDUCE_TO_COMPLEMENT,
	}
	
	/**
	 * Modified ddmin with heuristic that tries to remove elements from back to front.
	 */
	public static final DDMinMinimizer DEFAULT = new DDMinMinimizer();
	/**
	 * Original ddmin algorithm as descriped in the paper. Individual subsets are returned front to back (effectively
	 * removes large parts back to front), and complements are returned in the same order (effectively removes smaller
	 * parts front to back)
	 */
	public static final DDMinMinimizer PAPER = new DDMinMinimizer(Option.STRICT_COMPLEMENT_ORDER);
	
	/**
	 * This is similar to a binary search with a queue, i.e. it tries to remove parts of decreasing size, starting at
	 * half the input down to single elements. In contrast to the BinarySearchMinimizer the input is iterated repeatedly
	 * at increasing granularity and not only once.
	 */
	public static final DDMinMinimizer REMOVE_SUBSETS_OF_DECREASING_SIZE = new DDMinMinimizer(Option.SKIP_SUBSET_TESTS);
	public static final DDMinMinimizer REMOVE_SUBSETS_OF_DECREASING_SIZE_NONMINIMAL =
			new DDMinMinimizer(Option.SKIP_SUBSET_TESTS, Option.CONTINUE_AFTER_REDUCE_TO_COMPLEMENT);
	
	/**
	 * Remove single elements.
	 * Has absolutely nothing to do with ddmin anymore, but using this combination of options seems reasonable.
	 */
	public static final DDMinMinimizer REMOVE_SINGLE_ELEMENTS =
			new DDMinMinimizer(Option.SKIP_SUBSET_TESTS, Option.SKIP_TO_MAX_GRANULARITY);
	
	public static final DDMinMinimizer REMOVE_SINGLE_ELEMENTS_NONMINIMAL = new DDMinMinimizer(Option.SKIP_SUBSET_TESTS,
			Option.SKIP_TO_MAX_GRANULARITY, Option.CONTINUE_AFTER_REDUCE_TO_COMPLEMENT);
	
	private final EnumSet<Option> mOptions;
	
	/**
	 * Create new minimizer with the specified options.
	 *
	 * @param options
	 *            combination of options
	 */
	public DDMinMinimizer(final Option... options) {
		mOptions = options.length > 0 ? EnumSet.of(options[0], options) : EnumSet.noneOf(Option.class);
	}
	
	private static void checkInvariants(final int size, final int granularity, final int step) {
		if (size < 2) {
			throw new IllegalStateException(
					"circumstances already at minimum (empty test inputs are assumed to PASS and are not tested by "
					+ "ddmin)");
		}
		if (granularity < 2 || granularity > size) {
			throw new IllegalStateException("granularity out of bounds");
		}
		if (step < 0 || step >= granularity) {
			throw new IllegalStateException("iteration index out of bounds");
		}
	}
	
	final boolean continueAfterReduceToComplement() {
		return mOptions.contains(Option.CONTINUE_AFTER_REDUCE_TO_COMPLEMENT);
	}
	
	@Override
	public <E> IMinimizerStep<E> create(final List<E> input) {
		final int size = input.size();
		if (size < 2) {
			return createFinalStep(input);
		}
		return createNextStep(input, initialGranularity(size), skipSubsetTests(), 0);
	}
	
	private static <E> IMinimizerStep<E> createFinalStep(final List<E> minCircumstances) {
		return new FinalMinimizerStep<>(minCircumstances);
	}
	
	private <E> IMinimizerStep<E> createNextStep(final List<E> minCircumstances, final int granularity,
			final boolean checkComplements, final int step) {
		final int size = minCircumstances.size();
		checkInvariants(size, granularity, step);
		
		final int subsequenceIndex =
				iterateComplementsInReverse() && checkComplements ? (granularity - step - 1) : step;
		final SequencePartitioner.SubsequenceBounds bounds =
				new SequencePartitioner(size, granularity).get(subsequenceIndex);
		final List<E> testInput = checkComplements
				? MinimizerListOps.subListComplement(minCircumstances, bounds.getBegin(), bounds.getEnd())
				: MinimizerListOps.subList(minCircumstances, bounds.getBegin(), bounds.getEnd());
		return new DdminStep<>(minCircumstances, testInput, granularity, checkComplements, step);
	}
	
	final int initialGranularity(final int size) {
		return mOptions.contains(Option.SKIP_TO_MAX_GRANULARITY) ? size : 2;
	}
	
	@Override
	public boolean isEachVariantUnique() {
		// Testing only complements at max granularity does not generate
		// duplicate test inputs
		// (while still ensuring one-minimalality).
		return mOptions.contains(Option.SKIP_SUBSET_TESTS) && mOptions.contains(Option.SKIP_TO_MAX_GRANULARITY);
	}
	
	@Override
	public boolean isResultMinimal() {
		return !mOptions.contains(Option.CONTINUE_AFTER_REDUCE_TO_COMPLEMENT);
	}
	
	final boolean iterateComplementsInReverse() {
		return !mOptions.contains(Option.STRICT_COMPLEMENT_ORDER);
	}
	
	final boolean skipSubsetTests() {
		return mOptions.contains(Option.SKIP_SUBSET_TESTS);
	}
	
	/**
	 * Default instances.
	 * 
	 * @param <E>
	 *            element type
	 */
	class DdminStep<E> implements IMinimizerStep<E> {
		private final List<E> mMinCircumstances;
		private final List<E> mTestInput;
		private final int mGranularity;
		private final boolean mCheckComplements;
		private final int mIterationStep;
		
		DdminStep(final List<E> minCircumstances, final List<E> testInput, final int granularity,
				final boolean checkComplements, final int step) {
			mMinCircumstances = minCircumstances;
			mTestInput = testInput;
			mGranularity = granularity;
			mCheckComplements = checkComplements;
			mIterationStep = step;
		}
		
		@Override
		public List<E> getResult() {
			return mMinCircumstances;
		}
		
		@Override
		public List<E> getVariant() {
			return mTestInput;
		}
		
		@Override
		public boolean isDone() {
			return false;
		}
		
		@Override
		public IMinimizerStep<E> next(final boolean keepVariant) {
			return keepVariant ? reduceToCurrentTestInput() : tryNextTestInput();
		}
		
		private IMinimizerStep<E> reduceToCurrentTestInput() {
			final int size = mTestInput.size();
			if (size < 2) {
				return createFinalStep(mTestInput);
			}
			
			// Optionally continue with checking the complement of the next
			// subset instead of restarting a full iteration at the first
			// subset
			if (continueAfterReduceToComplement() && mCheckComplements) {
				return reduceToCurrentTestInputContinueWithNextComplement();
			}
			
			return createNextStep(mTestInput,
					mCheckComplements ? Math.max(mGranularity - 1, 2) : initialGranularity(size),
					skipSubsetTests(), 0);
		}
		
		private IMinimizerStep<E> reduceToCurrentTestInputContinueWithNextComplement() {
			if (mIterationStep < mGranularity - 1 && mGranularity > 2) {
				return createNextStep(mTestInput, mGranularity - 1, true, mIterationStep);
			}
			
			// increase granularity
			final int size = mTestInput.size();
			if (mGranularity - 1 < size) {
				return createNextStep(mTestInput, Math.toIntExact(Math.min(2L * (mGranularity - 1), size)),
						skipSubsetTests(), 0);
			}
			
			return createFinalStep(mTestInput);
		}
		
		private IMinimizerStep<E> tryNextTestInput() {
			// Increment iteration step
			if (mIterationStep + 1 < mGranularity) {
				return createNextStep(mMinCircumstances, mGranularity, mCheckComplements, mIterationStep + 1);
			}
			
			// Toggle complement setting and iterate again (unless granularity
			// is 2, in which case the two subsets are equal to their two
			// complements and have already been checked)
			if (!mCheckComplements && mGranularity != 2) {
				return createNextStep(mMinCircumstances, mGranularity, true, 0);
			}
			
			// Increase the granularity if it is not at the maximum yet
			final int size = mMinCircumstances.size();
			if (mGranularity < size) {
				return createNextStep(mMinCircumstances, Math.toIntExact(Math.min(2L * mGranularity, size)),
						skipSubsetTests(), 0);
			}
			
			return createFinalStep(mMinCircumstances);
		}
	}
}
