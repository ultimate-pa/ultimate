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

import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.ISearchStep;

/**
 * Monitors events during the speculative iteration. Decouples speculative iteration from the main iteration over steps
 * that are based on real test results.
 *
 * @param <T>
 *            search step type
 */
public interface ISpeculativeIterationObserver<T extends ISearchStep<?, T>> {
	/**
	 * Called when a canceled speculative step, that turned out to be invalid is completed with a result.
	 *
	 * @param step
	 *            step
	 * @param keepVariant
	 *            result
	 */
	default void onCanceledStepComplete(final T step, final boolean keepVariant) {
		// do nothing by default
	}
	
	/**
	 * Called when the non-speculative iteration is complete, i.e. step.isDone() is true.
	 *
	 * @param step
	 *            step
	 */
	default void onSearchComplete(final T step) {
		// do nothing by default
	}
	
	/**
	 * Called when the non-speculative iteration reaches the a new step. Always called before onStepComplete.
	 *
	 * @param step
	 *            step
	 */
	default void onStepBegin(final T step) {
		// do nothing by default
	}
	
	/**
	 * Called when the non-speculative iteration completes a step. Always called after onStepBegin.
	 *
	 * @param step
	 *            step
	 * @param keepVariant
	 *            result
	 */
	default void onStepComplete(final T step, final boolean keepVariant) {
		// do nothing by default
	}
	
	/**
	 * Called when a number of pending speculative tasks have been canceled because they turned out to be invalid.
	 *
	 * @param tasks
	 *            canceled tasks
	 */
	default void onTasksCanceled(final List<? extends ISpeculativeTask<T>> tasks) {
		// do nothing by default
	}
}
