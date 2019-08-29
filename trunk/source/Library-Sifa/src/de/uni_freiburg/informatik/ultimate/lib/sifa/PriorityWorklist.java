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

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

/**
 * Priority queue which saves pairs of generic entries (W, I) where W is called <i>work</i> I is called <i>input</i>.
 * Entries are sorted according to a custom order on the work entries. Only work entries listed in the
 * custom order can be added to this queue.
 *
 * @author schaetzc@tf.uni-freiburg.de
 *
 * @param <W>
 *            Type of the work entries
 * @param <I>
 *            Type of the input entries
 */
public class PriorityWorklist<W, I> implements IWorklistWithInputs<W, I> {

	/** Custom order for work entries. Entries with lower indices have higher priorities. */
	private final List<W> mIdxToWork;
	/** Maps work entries to their indices in {@link #mIdxToWork}. */
	private final Map<W, Integer> mWorkToIdx = new HashMap<>();
	/**
	 * The actual priority queue.
	 * Instead of the pair (W,I) only the index of W in {@link #mIdxToWork} is stored
	 * and used as a priority. Use {@link #mIdxToWork} to retrieve the work component
	 * and {@link #mInputsForElemsInWorklist} to retrieve the input component.
	 */
	private final PriorityQueue<Integer> mWorklistOfIndices = new PriorityQueue<>();
	/** For each entry in {@link #mWorklistOfIndices} map the work items to their inputs. */
	private final Map<Integer, I> mInputsForElemsInWorklist = new HashMap<>();
	private final BiFunction<I, I, I> mMergeFunction;
	/** Work component from entry last retrieved by {@link #advance()}. */
	private W mCurrentWork;
	/** Input component from entry last retrieved by {@link #advance()}. */
	private I mCurrentInput;

	/**
	 * Creates a new priority worklist based on a custom order on the work entries.
	 *
	 * @param order
	 *            Order on the work entry. The first (index 0) element has the highest priority.
	 * @param mergeFunction
	 *            Function used to merge two inputs when an already enqueued work entry is added again.
	 */
	public PriorityWorklist(final List<W> order, final BiFunction<I, I, I> mergeFunction) {
		mIdxToWork = order;
		order.forEach(node -> mWorkToIdx.put(node, mWorkToIdx.size()));
		mMergeFunction = mergeFunction;
	}

	/**
	 * Adds or updates an entry. Only work entries listed in the custom order can be added. If {@code work} is already
	 * queued, its old and new input are merged and its position is kept. If {@code work} is new to this queue, inserts
	 * it corresponding to its priority.
	 *
	 * @param workIdx
	 *            Work entry
	 * @param newInput
	 *            Input for work entry
	 */
	@Override
	public void add(final W work, final I newInput) {
		final Integer index = mWorkToIdx.get(work);
		if (index == null) {
			throw new IllegalArgumentException("Tried to insert element unknown in custom order: " + work);
		}
		mInputsForElemsInWorklist.compute(index, (key, oldInput) -> addInternal(key, oldInput, newInput));
	}

	private I addInternal(final Integer index, final I oldInput, final I newInput) {
		if (oldInput != null) {
			return mMergeFunction.apply(oldInput, newInput);
		}
		mWorklistOfIndices.add(index);
		return newInput;
	}

	@Override
	public boolean advance() {
		if (mWorklistOfIndices.isEmpty()) {
			return false;
		}
		final Integer index = mWorklistOfIndices.poll();
		mCurrentWork = mIdxToWork.get(index);
		mCurrentInput = mInputsForElemsInWorklist.remove(index);
		return true;
	}

	@Override
	public W getWork() {
		return mCurrentWork;
	}

	@Override
	public I getInput() {
		return mCurrentInput;
	}

	@Override
	public String toString() {
		return mWorklistOfIndices.stream().sorted(mWorklistOfIndices.comparator()).map(this::workIdxToString)
				.collect(Collectors.joining("\n"));
	}

	private String workIdxToString(final Integer workIdx) {
		return String.format("%s=%s", mIdxToWork.get(workIdx), mInputsForElemsInWorklist.get(workIdx));
	}

}
