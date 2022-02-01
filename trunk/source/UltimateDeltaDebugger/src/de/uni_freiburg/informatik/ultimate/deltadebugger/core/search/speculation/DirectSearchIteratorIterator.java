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

import java.util.Optional;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.MissingTestResultException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.ISearchStep;

/**
 * Single threaded counterpart to the {@link ParallelSearchIteratorIterator}.
 *
 * @param <T>
 *            search step type
 */
public class DirectSearchIteratorIterator<T extends ISearchStep<?, T>> {
	private final SpeculativeSearchIterator<T> mSearchIterator;
	private final ICancelableStepTest<T> mCancelableTest;
	
	/**
	 * Constructs a new instance that can be used for one iteration.
	 *
	 * @param searchIterator
	 *            speculative iterator to work on
	 * @param cancelableTest
	 *            test function that is called to determine test results
	 */
	public DirectSearchIteratorIterator(final SpeculativeSearchIterator<T> searchIterator,
			final ICancelableStepTest<T> cancelableTest) {
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
	 *            timeout
	 * @param unit
	 *            time unit
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
	 * @return The step reached at the end of iteration.
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
			// A test is only allowed to return no result if cancellation
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
