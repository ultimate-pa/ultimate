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
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.CancellationException;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.function.BooleanSupplier;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.MissingTestResultException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.UncheckedInterruptedException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.ISearchStep;

/**
 * Runs a speculative search on an arbitrary number of worker threads with a given test function.
 *
 * @param <T>
 *            search step type
 */
public class ParallelSearchIteratorIterator<T extends ISearchStep<?, T>> {
	private static final int SLEEP_TIME_MILLISEC = 10;
	
	private final SpeculativeSearchIterator<T> mSearchIterator;
	private final ICancelableStepTest<T> mCancelableTest;
	private final List<Future<?>> mPendingWorkers = new ArrayList<>();
	private volatile boolean mStopRequested;
	
	/**
	 * Constructs a new instance that can be used for one iteration.
	 * Note that all concurrent access to the SpeculativeSearchIterator is synchronized on the searchIterator instance
	 * and only the test function if executed without any synchronization.
	 *
	 * @param searchIterator
	 *            speculative iterator to work on
	 * @param cancelableTest
	 *            test function that is called to determine test results
	 */
	public ParallelSearchIteratorIterator(final SpeculativeSearchIterator<T> searchIterator,
			final ICancelableStepTest<T> cancelableTest) {
		this.mSearchIterator = searchIterator;
		this.mCancelableTest = cancelableTest;
	}
	
	/**
	 * Start iteration using the given number of worker threads that are started by the given executor service.
	 *
	 * @param executorService
	 *            executor service
	 * @param workerCount
	 *            number of workers
	 */
	public void beginIteration(final ExecutorService executorService, final int workerCount) {
		if (workerCount < 1) {
			throw new IllegalArgumentException();
		}
		if (!mPendingWorkers.isEmpty()) {
			throw new IllegalStateException("beginIteration already called");
		}
		for (int i = 0; i != workerCount; ++i) {
			mPendingWorkers.add(executorService.submit(this::worker));
		}
	}
	
	/**
	 * Wait until iteration has ended and return the result.
	 *
	 * @return current result.
	 * @throws InterruptedException
	 *             if a worker thread was interrupted while waiting
	 */
	public T endIteration() throws InterruptedException {
		if (mPendingWorkers.isEmpty()) {
			throw new IllegalStateException("beginIteration has not been called");
		}
		
		// Wait for all workers to return.
		// This is important to ensure that
		// - no exceptions are swallowed
		// - no new (potentially expensive) tests are started before the
		// previous ones have completed
		// - all parallel execution is limited to this method
		try {
			for (final Future<?> f : mPendingWorkers) {
				f.get();
			}
		} catch (final ExecutionException e) {
			final Throwable inner = e.getCause();
			if (inner instanceof Error) {
				throw (Error) inner;
			}
			if (inner instanceof RuntimeException) {
				throw (RuntimeException) inner;
			}
			throw new RuntimeException("unexpected sneaky exception", e);
		}
		
		return getCurrentStep();
	}
	
	/**
	 * @return The current step of the non-speculative iteration.
	 */
	public T getCurrentStep() {
		synchronized (mSearchIterator) {
			return mSearchIterator.getCurrentStep();
		}
	}
	
	private ISpeculativeTask<T> getNextTask() {
		while (true) {
			synchronized (mSearchIterator) {
				final ISpeculativeTask<T> task = mSearchIterator.getNextTask();
				if (task != null) {
					return task;
				}
			}
			
			// Currently there is no speculative step available,
			// but not all pending tasks have completed yet so there
			// may be further steps available later
			// -> wait for more tasks to complete
			// Should use a more sophisticated event mechanism to wake
			// up once another task has completed, and also ensure
			// that there is another task pending...
			try {
				TimeUnit.MILLISECONDS.sleep(SLEEP_TIME_MILLISEC);
			} catch (final InterruptedException e) {
				// There is no expected interruption, if this happens it's
				// like any other unexpected runtime exception
				Thread.currentThread().interrupt();
				throw new UncheckedInterruptedException(e);
			}
		}
	}
	
	public boolean isStopRequested() {
		return mStopRequested;
	}
	
	/**
	 * Begin and wait for iteration to end, then return the step.
	 *
	 * @param executorService
	 *            executor service
	 * @param workerCount
	 *            number of workers
	 * @return the step reached at the end of iteration
	 */
	public T iterateToEnd(final ExecutorService executorService, final int workerCount) {
		beginIteration(executorService, workerCount);
		try {
			return endIteration();
		} catch (final InterruptedException unexpected) {
			Thread.currentThread().interrupt();
			throw new UncheckedInterruptedException(unexpected);
		}
	}
	
	/**
	 * Checks if iteration has ended (either successfully or non-successfully) without blocking.
	 *
	 * @return true if iteration has ended
	 */
	public boolean pollIsDone() {
		if (mPendingWorkers.isEmpty()) {
			throw new IllegalStateException("beginIteration has not been called");
		}
		return mPendingWorkers.stream().allMatch(Future::isDone);
	}
	
	private void runTestAndCompleteTask(final ISpeculativeTask<T> task) {
		final BooleanSupplier isCanceled = () -> task.isCanceled() || isStopRequested();
		final Optional<Boolean> result = mCancelableTest.test(task.getStep(), isCanceled);
		if (!result.isPresent()) {
			// A test is only allowed to return no result if cancelation
			// was actually requested. To handle this case we could only
			// abort the whole iteration or repeat the test.
			// Iteration control is not the responsibility of the test
			// function and repeating the test with a broken
			// test function sounds like bad idea.
			if (!isCanceled.getAsBoolean()) {
				throw new MissingTestResultException();
			}
			return;
		}
		synchronized (mSearchIterator) {
			task.complete(result.get());
		}
	}
	
	/**
	 * Request workers to stop the iteration.
	 */
	public void stopWorkers() {
		mStopRequested = true;
	}
	
	/**
	 * Wait until iteration has ended for a limited time span only.
	 *
	 * @param timeout
	 *            timeout
	 * @param unit
	 *            time unit
	 * @return true if all workers have ended at the time of return
	 * @throws InterruptedException
	 *             if a worker thread was interrupted while waiting
	 */
	public boolean waitForEnd(final long timeout, final TimeUnit unit) throws InterruptedException {
		long nanosLeft = unit.toNanos(timeout);
		final long deadline = System.nanoTime() + nanosLeft;
		
		for (final Future<?> f : mPendingWorkers) {
			if (!f.isDone()) {
				if (nanosLeft <= 0L) {
					return false;
				}
				try {
					f.get(nanosLeft, TimeUnit.NANOSECONDS);
				} catch (CancellationException | ExecutionException e) {
					// deferr exception to endIteration
				} catch (final TimeoutException e) {
					return false;
				}
				nanosLeft = deadline - System.nanoTime();
			}
		}
		return true;
	}
	
	private void worker() {
		try {
			while (!isStopRequested()) {
				final ISpeculativeTask<T> task = getNextTask();
				if (task.isDone()) {
					return;
				}
				runTestAndCompleteTask(task);
			}
		} catch (final Exception e) {
			stopWorkers();
			throw e;
		}
	}
}
