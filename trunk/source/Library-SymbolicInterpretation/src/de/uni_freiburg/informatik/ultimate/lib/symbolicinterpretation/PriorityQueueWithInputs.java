/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation;

import java.util.function.BiFunction;
import java.util.function.ToIntFunction;

/**
 * Priority queue with a fixed number of priority levels [0, n] with n >= 0; 0 is the highest priority.
 * The queue saves pairs of generic entries (W, I) where W is called <i>work</i> I is called <i>input</i>.
 * Work entries can be in queue at most once. When adding an already queued work entry again (with a possible
 * different input) the old and the new input are merged using a user-specified merge function.
 * 
 * @author schaetzc@tf.uni-freiburg.de
 *
 * @param <W> Type of the work entries
 * @param <I> Type of the input entries
 */
public class PriorityQueueWithInputs<W, I> implements IWorklistWithInputs<W, I> {

	private final FifoWithInputs<W, I>[] mWorklists;
	private final ToIntFunction<W> mPriorityLevelOf;
	private int mAdvancedPrio = -1;

	/**
	 * Creates a new priority queue with a fixed number of priority levels.
	 * 
	 * @param priorityLevels Number of priority levels for this queue.
	 * @param priorityLevelOf Maps work entries to their priorities. The priority has to be deterministic.
	 *                        Priority levels are [0, priorityLevels). 0 is the highest priority.
	 * @param mergeFunction When an already enqueued work entry is added again this function is called to compute a
	 *                      new input from the already enqueued input and the to be enqueued input.
	 *                      The form is {@code (oldInput, newInput) -> mergedInput}.
	 */
	@SuppressWarnings("unchecked")
	public PriorityQueueWithInputs(final int priorityLevels, final ToIntFunction<W> priorityLevelOf,
			final BiFunction<I, I, I> mergeFunction) {
		mWorklists = (FifoWithInputs<W, I>[]) new FifoWithInputs[priorityLevels];
		mPriorityLevelOf = priorityLevelOf;
		for (int prio = 0; prio < priorityLevels; ++prio) {
			mWorklists[prio] = new FifoWithInputs<>(mergeFunction);
		}
	}

	/**
	 * Adds or updates an entry.
	 * If {@code work} is already queued, its old and new input are merged and its position is kept.
	 * If {@code work} is new to this queue, adds it to the tail of the internal queue with corresponding priority.
	 * 
	 * @param work Work entry
	 * @param addInput Input for work entry
	 */
	@Override
	public void add(final W work, final I addInput) {
		mWorklists[mPriorityLevelOf.applyAsInt(work)].add(work, addInput);
	}

	@Override
	public boolean advance() {
		for (int prio = 0; prio < mWorklists.length; ++prio) {
			if (mWorklists[prio].advance()) {
				mAdvancedPrio = prio;
				return true;
			}
		}
		return false;
	}

	@Override
	public W getWork() {
		ensureAdvanced();
		return mWorklists[mAdvancedPrio].getWork();
	}

	@Override
	public I getInput() {
		ensureAdvanced();
		return mWorklists[mAdvancedPrio].getInput();
	}

	private void ensureAdvanced() {
		if (mAdvancedPrio < 0) {
			throw new IllegalStateException("Never called advance() on this worklist.");
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		for (int prio = 0; prio < mWorklists.length; ++prio) {
			sb.append("prio ").append(prio).append(" = ").append(mWorklists[prio]).append("\n");
		}
		return sb.toString();
	}

}
