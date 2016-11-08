package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.ISearchStep;

/**
 * Monitors events during the speculative iteration. Decouples speculative iteration from the main iteration over steps
 * that are based on real test results.
 *
 * @param <T>
 */
public interface ISpeculativeIterationObserver<T extends ISearchStep<?, T>> {

	/**
	 * Called when a canceled speculative step, that turned out to be invalid is completed with a result.
	 *
	 * @param step
	 * @param keepVariant
	 *            result
	 */
	default void onCanceledStepComplete(final T step, final boolean keepVariant) {
	}

	/**
	 * Called when the non-speculative iteration is complete, i.e. step.isDone() is true.
	 *
	 * @param step
	 */
	default void onSearchComplete(final T step) {
	}

	/**
	 * Called when the non-speculative iteration reaches the a new step. Always called before onStepComplete.
	 *
	 * @param step
	 */
	default void onStepBegin(final T step) {
	}

	/**
	 * Called when the non-speculative iteration completes a step. Always called after onStepBegin.
	 *
	 * @param step
	 * @param keepVariant
	 *            result
	 */
	default void onStepComplete(final T step, final boolean keepVariant) {
	}

	/**
	 * Called when a number of pending speculative tasks have been canceled because they turned out to be invalid.
	 *
	 * @param tasks
	 *            canceled tasks
	 */
	default void onTasksCanceled(final List<? extends ISpeculativeTask<T>> tasks) {
	}

}
