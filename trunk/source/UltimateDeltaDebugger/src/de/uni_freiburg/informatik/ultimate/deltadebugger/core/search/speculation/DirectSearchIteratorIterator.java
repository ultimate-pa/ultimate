package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation;

import java.util.Optional;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.MissingTestResultException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.ISearchStep;

/**
 * Single threaded counterpart to the ParallelSearchIteratorIterator.
 *
 * @param <T>
 *            search step type
 */
public class DirectSearchIteratorIterator<T extends ISearchStep<?, T>> {
	private final SpeculativeSearchIterator<T> mSearchIterator;
	private final CancelableStepTest<T> mCancelableTest;

	/**
	 * Constructs a new instance that can be used for one iteration.
	 *
	 * @param searchIterator
	 *            speculative iterator to work on
	 * @param cancelableTest
	 *            test function that is called to determine test results
	 */
	public DirectSearchIteratorIterator(final SpeculativeSearchIterator<T> searchIterator,
			final CancelableStepTest<T> cancelableTest) {
		mSearchIterator = searchIterator;
		mCancelableTest = cancelableTest;
	}

	public T getCurrentStep() {
		return mSearchIterator.getCurrentStep();
	}

	/**
	 * Iterates for a certain time limit.
	 *
	 * @param timeout
	 * @param unit
	 * @return true iff iteration has ended
	 */
	public boolean iterateFor(final long timeout, final TimeUnit unit) {
		final long deadline = System.currentTimeMillis() + unit.toMillis(timeout);
		do {
			final ISpeculativeTask<T> task = mSearchIterator.getNextTask();
			if (task.isDone()) {
				return true;
			}
			runTestAndCompleteTask(task);
		} while (System.currentTimeMillis() < deadline);

		return false;
	}

	/**
	 * @return the step reached at the end of iteration
	 */
	public T iterateToEnd() {
		while (true) {
			final ISpeculativeTask<T> task = mSearchIterator.getNextTask();
			if (task.isDone()) {
				return task.getStep();
			}
			runTestAndCompleteTask(task);
		}
	}

	private void runTestAndCompleteTask(final ISpeculativeTask<T> task) {
		final Optional<Boolean> result = mCancelableTest.test(task.getStep(), task::isCanceled);
		if (!result.isPresent()) {
			// A test is only allowed to return no result if cancelation
			// was actually requested. To handle this case we could only
			// abort the whole iteration or repeat the test.
			// Iteration control is not the responsibility of the test
			// function and repeating the test with a broken
			// test function sounds like bad idea.
			if (!task.isCanceled()) {
				throw new MissingTestResultException();
			}
			return;
		}

		task.complete(result.get());
	}

}
