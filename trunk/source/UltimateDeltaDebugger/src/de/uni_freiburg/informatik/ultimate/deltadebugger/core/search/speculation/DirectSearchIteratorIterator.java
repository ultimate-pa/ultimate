package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation;

import java.util.Optional;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.MissingTestResultException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.SearchStep;

/**
 * Single threaded counterpart to the ParallelSearchIteratorIterator.
 *
 * @param <T>
 *            search step type
 */
public class DirectSearchIteratorIterator<T extends SearchStep<?, T>> {
	private final SpeculativeSearchIterator<T> searchIterator;
	private final CancelableStepTest<T> cancelableTest;

	/**
	 * Constructs a new instance that can be used for one iteration.
	 * 
	 * @param searchIterator
	 *            speculative iterator to work on
	 * @param cancelableTest
	 *            test function that is called to determine test results
	 */
	public DirectSearchIteratorIterator(SpeculativeSearchIterator<T> searchIterator,
			CancelableStepTest<T> cancelableTest) {
		this.searchIterator = searchIterator;
		this.cancelableTest = cancelableTest;
	}

	public T getCurrentStep() {
		return searchIterator.getCurrentStep();
	}

	/**
	 * @return the step reached at the end of iteration
	 */
	public T iterateToEnd() {
		while (true) {
			final SpeculativeTask<T> task = searchIterator.getNextTask();
			if (task.isDone()) {
				return task.getStep();
			}
			runTestAndCompleteTask(task);
		}
	}

	/**
	 * Iterates for a certain time limit.
	 * 
	 * @param timeout
	 * @param unit
	 * @return true iff iteration has ended
	 */
	public boolean iterateFor(long timeout, TimeUnit unit) {
		final long deadline = System.currentTimeMillis() + unit.toMillis(timeout);
		do {
			final SpeculativeTask<T> task = searchIterator.getNextTask();
			if (task.isDone()) {
				return true;
			}
			runTestAndCompleteTask(task);
		} while (System.currentTimeMillis() < deadline);

		return false;
	}

	private void runTestAndCompleteTask(SpeculativeTask<T> task) {
		final Optional<Boolean> result = cancelableTest.test(task.getStep(), task::isCanceled);
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