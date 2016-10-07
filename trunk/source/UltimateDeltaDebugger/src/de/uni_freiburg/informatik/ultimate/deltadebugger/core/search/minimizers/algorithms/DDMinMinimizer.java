package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms;

import java.util.EnumSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.Minimizer;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.MinimizerStep;

/**
 * Minimizer based on the original ddmin algorithm. Several options have been
 * added to adjust the order and overall amount generated test inputs.
 * 
 * <ul>
 * <li>The empty set is not considered a valid test input by ddmin and hence not
 * returned by this minimizer.
 * <li>In contrast to the original algorithm subsets are removed back to front
 * by default.
 * </ul>
 */
public class DDMinMinimizer implements Minimizer {

	/**
	 * Default instances
	 */

	/**
	 * ddmin with heuristic that tries to remove elements from back to front.
	 */
	public static final DDMinMinimizer DEFAULT = new DDMinMinimizer();

	/**
	 * Original ddmin algorithm as descriped in the paper. Individual subsets
	 * are returned front to back (effectively removes large parts back to
	 * front), and complements are returned in the same order (effectively
	 * removes smaller parts front to back)
	 */
	public static final DDMinMinimizer PAPER = new DDMinMinimizer(Option.STRICT_COMPLEMENT_ORDER);

	/**
	 * This is similar to a binary search with a queue, i.e. it tries to remove
	 * parts of decreasing size, starting at half the input down to single
	 * elements. In contrast to the BinarySearchMinimizer the input is iterated
	 * repeatedly at increasing granularity and not only once.
	 */
	public static final DDMinMinimizer REMOVE_SUBSETS_OF_DECREASING_SIZE = new DDMinMinimizer(Option.SKIP_SUBSET_TESTS);
	public static final DDMinMinimizer REMOVE_SUBSETS_OF_DECREASING_SIZE_NONMINIMAL = new DDMinMinimizer(
			Option.SKIP_SUBSET_TESTS, Option.CONTINUE_AFTER_REDUCE_TO_COMPLEMENT);

	/**
	 * Remove single elements.
	 * 
	 * Has absolutely nothing to do with ddmin anymore, but using this
	 * combination of options seems reasonable.
	 */
	public static final DDMinMinimizer REMOVE_SINGLE_ELEMENTS = new DDMinMinimizer(Option.SKIP_SUBSET_TESTS,
			Option.SKIP_TO_MAX_GRANULARITY);
	public static final DDMinMinimizer REMOVE_SINGLE_ELEMENTS_NONMINIMAL = new DDMinMinimizer(Option.SKIP_SUBSET_TESTS,
			Option.SKIP_TO_MAX_GRANULARITY, Option.CONTINUE_AFTER_REDUCE_TO_COMPLEMENT);

	
	/**
	 * Options.
	 */
	public enum Option {

		/**
		 * In the original ddmin definition complements of subsets are checked
		 * in the same order as the corresponding subsets. This implementation
		 * checks complements in reverse order, i.e. subsets are iterated back
		 * to front in order to remove elements at the back first. This small
		 * difference is useful if elements are more likely to depend on
		 * preceding elements than the other way around. This flag disables this
		 * heuristic and gives the original ddmin algorithm from the paper.
		 * Motivation: In a C source a declaration comes before any reference,
		 * so removing elements from front to back is more likely to cause
		 * compilations errors because declarations are removed before their
		 * references.
		 */
		STRICT_COMPLEMENT_ORDER,

		/**
		 * Do not test single subsets, only complements thereof. The resulting
		 * algorithm is similar to a binary search but with a queue instead of a
		 * stack, i.e. the removal of larger subsets is always tested before
		 * smaller subsets and the size of test inputs may decrease faster.
		 * Motivation: Reduction to a single subset at higher granularities may
		 * be unlikely to succeed for certain inputs (but is repeated after each
		 * successful reduction to a complement). Skipping this iteration
		 * improves worst case performance and is still one-minimal.
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

	private final EnumSet<Option> options;

	/**
	 * Create new minimizer with the specified options.
	 * 
	 * @param options
	 *            combination of options
	 */
	public DDMinMinimizer(Option... options) {
		this.options = options.length > 0 ? EnumSet.of(options[0], options) : EnumSet.noneOf(Option.class);
	}

	final boolean iterateComplementsInReverse() {
		return !options.contains(Option.STRICT_COMPLEMENT_ORDER);
	}

	final boolean skipSubsetTests() {
		return options.contains(Option.SKIP_SUBSET_TESTS);
	}

	final int initialGranularity(int size) {
		return options.contains(Option.SKIP_TO_MAX_GRANULARITY) ? size : 2;
	}

	final boolean continueAfterReduceToComplement() {
		return options.contains(Option.CONTINUE_AFTER_REDUCE_TO_COMPLEMENT);
	}

	@Override
	public <E> MinimizerStep<E> create(List<E> input) {
		final int size = input.size();
		if (size < 2) {
			return createFinalStep(input);
		}
		return createNextStep(input, initialGranularity(size), skipSubsetTests(), 0);
	}

	@Override
	public boolean isResultMinimal() {
		return !options.contains(Option.CONTINUE_AFTER_REDUCE_TO_COMPLEMENT);
	}

	@Override
	public boolean isEachVariantUnique() {
		// Testing only complements at max granularity does not generate
		// duplicate test inputs
		// (while still ensuring one-minimalality).
		return options.contains(Option.SKIP_SUBSET_TESTS) && options.contains(Option.SKIP_TO_MAX_GRANULARITY);
	}

	private <E> MinimizerStep<E> createNextStep(List<E> minCircumstances, int granularity, boolean checkComplements,
			int step) {
		final int size = minCircumstances.size();
		checkInvariants(size, granularity, step);

		final int subsequenceIndex = iterateComplementsInReverse() && checkComplements ? granularity - step - 1 : step;
		final SequencePartitioner.SubsequenceBounds bounds = new SequencePartitioner(size, granularity).get(subsequenceIndex);
		final List<E> testInput = checkComplements
				? MinimizerListOps.subListComplement(minCircumstances, bounds.getBegin(), bounds.getEnd())
				: MinimizerListOps.subList(minCircumstances, bounds.getBegin(), bounds.getEnd());
		return new DDMinStep<>(minCircumstances, testInput, granularity, checkComplements, step);
	}

	private <E> MinimizerStep<E> createFinalStep(List<E> minCircumstances) {
		return new FinalMinimizerStep<>(minCircumstances);
	}

	private void checkInvariants(int size, int granularity, int step) {
		if (size < 2) {
			throw new IllegalStateException(
					"circumstances already at minimum (empty test inputs are assumed to PASS and are not tested by ddmin)");
		}
		if (granularity < 2 || granularity > size) {
			throw new IllegalStateException("granularity out of bounds");
		}
		if (step < 0 || step >= granularity) {
			throw new IllegalStateException("iteration index out of bounds");
		}
	}

	class DDMinStep<E> implements MinimizerStep<E> {
		final List<E> minCircumstances;
		final List<E> testInput;
		final int granularity;
		final boolean checkComplements;
		final int iterationStep;

		DDMinStep(List<E> minCircumstances, List<E> testInput, int granularity, boolean checkComplements, int step) {
			this.minCircumstances = minCircumstances;
			this.testInput = testInput;
			this.granularity = granularity;
			this.checkComplements = checkComplements;
			this.iterationStep = step;
		}

		@Override
		public boolean isDone() {
			return false;
		}

		@Override
		public List<E> getVariant() {
			return testInput;
		}

		@Override
		public MinimizerStep<E> next(boolean keepVariant) {
			return keepVariant ? reduceToCurrentTestInput() : tryNextTestInput();
		}

		@Override
		public List<E> getResult() {
			return minCircumstances;
		}

		private MinimizerStep<E> reduceToCurrentTestInput() {
			final int size = testInput.size();
			if (size < 2) {
				return createFinalStep(testInput);
			}

			// Optionally continue with checking the complement of the next
			// subset instead of restarting a full iteration at the first
			// subset
			if (continueAfterReduceToComplement() && checkComplements) {
				return reduceToCurrentTestInputContinueWithNextComplement();
			}

			return createNextStep(testInput, checkComplements ? Math.max(granularity - 1, 2) : initialGranularity(size),
					skipSubsetTests(), 0);
		}

		private MinimizerStep<E> reduceToCurrentTestInputContinueWithNextComplement() {
			if (iterationStep < granularity - 1 && granularity > 2) {
				return createNextStep(testInput, granularity - 1, true, iterationStep);
			}

			// increase granularity
			final int size = testInput.size();
			if (granularity - 1 < size) {
				return createNextStep(testInput, Math.toIntExact(Math.min(2L * (granularity - 1), size)),
						skipSubsetTests(), 0);
			}

			return createFinalStep(testInput);
		}

		private MinimizerStep<E> tryNextTestInput() {
			// Increment iteration step
			if (iterationStep + 1 < granularity) {
				return createNextStep(minCircumstances, granularity, checkComplements, iterationStep + 1);
			}

			// Toggle complement setting and iterate again (unless granularity
			// is 2, in which case the two subsets are equal to their two
			// complements and have already been checked)
			if (!checkComplements && granularity != 2) {
				return createNextStep(minCircumstances, granularity, true, 0);
			}

			// Increase the granularity if it is not at the maximum yet
			final int size = minCircumstances.size();
			if (granularity < size) {
				return createNextStep(minCircumstances, Math.toIntExact(Math.min(2L * granularity, size)),
						skipSubsetTests(), 0);
			}

			return createFinalStep(minCircumstances);
		}
	}

}
