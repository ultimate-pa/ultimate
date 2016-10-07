package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.SearchStep;

/**
 * Represents a task during a speculative search iteration, i.e. a search step
 * that has to be tested and eventually to be completed by reporting the result.
 * The contained step may be a speculative step that depends on the assumption
 * that the test for a previous step fails.
 * 
 * As soon it turns out that speculation was wrong steps are canceled and
 * isCanceled() returns true. This can be called to abort the test if possible,
 * because it's result is not of use anymore. If and only if a step is canceled
 * the called to complete is optional - otherwise it must be called or the
 * iteration will not advance.
 * 
 * Getters are thread safe, complete() is NOT and must be synchronized with
 * other methods of the originating SpeculativeSearchIterator instance.
 *
 * @param <T>
 *            type of algorithm step
 */
public interface SpeculativeTask<T extends SearchStep<?, T>> {

	/**
	 * @return whether the contained step is a final step
	 */
	boolean isDone();

	/**
	 * @return whether this step is canceled
	 */
	boolean isCanceled();

	/**
	 * @return the step
	 */
	T getStep();

	/**
	 * Completes the task with the given test result. Has to be called unless
	 * the step is canceled.
	 * 
	 * @param keepVariant
	 *            test result
	 */
	void complete(boolean keepVariant);

}