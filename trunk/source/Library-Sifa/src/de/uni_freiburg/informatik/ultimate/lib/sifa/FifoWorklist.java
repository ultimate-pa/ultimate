/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.BiFunction;

/**
 * FIFO queue which saves pairs of generic entries (W, I) where W is called <i>work</i> I is called <i>input</i>.
 * Work entries can be in queue at most once. When adding an already queued work entry again (with a possible
 * different input) the old and the new input are merged using a user-specified merge function.
 *
 * @author schaetzc@tf.uni-freiburg.de
 *
 * @param <W> Type of the work entries
 * @param <I> Type of the input entries
 */
public class FifoWorklist<W, I> implements IWorklistWithInputs<W, I> {

	private final BiFunction<I, I, I> mMergeFunction;
	private final Map<W, I> mWorklist = new LinkedHashMap<>();
	private Entry<W, I> mRemovedEntry;

	/**
	 * Creates a new queue.
	 *
	 * @param mergeFunction When an already enqueued work entry is added again this function is called to compute a
	 *                      new input from the already enqueued input and the to be enqueued input.
	 *                      The form is {@code (oldInput, newInput) -> mergedInput}.
	 */
	public FifoWorklist(final BiFunction<I, I, I> mergeFunction) {
		mMergeFunction = mergeFunction;
	}

	/**
	 * Adds or updates an entry.
	 * If {@code work} is already queued, its old and new input are merged and its position is kept.
	 * If {@code work} is new to this queue, adds it to the tail.
	 *
	 * @param work Work entry
	 * @param addInput Input for work entry
	 */
	@Override
	public void add(final W work, final I addInput) {
		mWorklist.merge(work, addInput, mMergeFunction);
	}

	/**
	 * If this queue contains entries, removes the head (oldest entry) from this queue.
	 * The removed entry can be queried with {@link #getWork()} and {@link #getInput()}.
	 * <p>
	 * Calling advance on an empty worklist has no effect.
	 *
	 * @return The queue contained at least one entry, the head was removed.
	 */
	@Override
	public boolean advance() {
		if (mWorklist.isEmpty()) {
			return false;
		}
		final Iterator<Entry<W, I>> iterator = mWorklist.entrySet().iterator();
		mRemovedEntry = iterator.next();
		iterator.remove();
		return true;
	}

	private void ensureAdvanced() {
		if (mRemovedEntry == null) {
			throw new IllegalStateException("Never called advance() on this worklist.");
		}
	}

	/**
	 * @see #advance()
	 */
	@Override
	public W getWork() {
		ensureAdvanced();
		return mRemovedEntry.getKey();
	}

	/**
	 * @see #advance()
	 */
	@Override
	public I getInput() {
		ensureAdvanced();
		return mRemovedEntry.getValue();
	}

	@Override
	public String toString() {
		return mWorklist.toString();
	}
}
