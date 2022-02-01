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

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.ISearchStep;

/**
 * Represents a task during a speculative search iteration, i.e. a search step that has to be tested and eventually to
 * be completed by reporting the result. The contained step may be a speculative step that depends on the assumption
 * that the test for a previous step fails.
 * As soon it turns out that speculation was wrong steps are canceled and isCanceled() returns true. This can be called
 * to abort the test if possible, because it's result is not of use anymore. If and only if a step is canceled the
 * called to complete is optional - otherwise it must be called or the iteration will not advance.
 * Getters are thread safe, complete() is NOT and must be synchronized with other methods of the originating
 * SpeculativeSearchIterator instance.
 *
 * @param <T>
 *            type of algorithm step
 */
public interface ISpeculativeTask<T extends ISearchStep<?, T>> {
	/**
	 * Completes the task with the given test result. Has to be called unless the step is canceled.
	 *
	 * @param keepVariant
	 *            test result
	 */
	void complete(boolean keepVariant);
	
	/**
	 * @return The step.
	 */
	T getStep();
	
	/**
	 * @return Whether this step is canceled.
	 */
	boolean isCanceled();
	
	/**
	 * @return Whether the contained step is a final step.
	 */
	boolean isDone();
}
