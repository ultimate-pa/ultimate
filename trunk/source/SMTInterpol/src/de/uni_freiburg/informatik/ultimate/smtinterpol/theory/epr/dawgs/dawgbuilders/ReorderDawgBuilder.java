/*
 * Copyright (C) 2016-2019 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgbuilders;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgStateFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;

/**
 * This creates a new Dawg where some columns are reordered and some new columns are introduced.
 *
 * @author Jochen Hoenicke
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class ReorderDawgBuilder<LETTER, VALUE, COLNAMES> extends DawgBuilder<LETTER> {
	private final DawgStateFactory<LETTER> mDawgStateFactory;
	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;
	private final Map<Pair<List<DawgLetter<LETTER>>, DawgState<LETTER, VALUE>>, DawgState<LETTER, VALUE>> mCache;
	private final Map<Set<DawgState<LETTER, VALUE>>, DawgState<LETTER, VALUE>> mUnionCache;

	public ReorderDawgBuilder(final DawgFactory<LETTER, COLNAMES> factory) {
		mDawgFactory = factory;
		mDawgStateFactory = mDawgFactory.getDawgStateFactory();
		mCache = new HashMap<>();
		mUnionCache = new HashMap<>();
	}

	private DawgState<LETTER, VALUE> addLettersInFront(final List<DawgLetter<LETTER>> partialWord,
			DawgState<LETTER, VALUE> state) {
		for (int i = partialWord.size() - 1; i >= 0; i--) {
			final DawgLetter<LETTER> ltr = partialWord.get(i);
			assert !ltr.isEmpty();
			state = mDawgStateFactory.createIntermediateState(Collections.singletonMap(state, ltr));
		}
		return state;
	}

	/**
	 * Build the union of the partial dawgs in the given set. The dawgs must not be defined for the same point. This
	 * returns a partial or total dawg that is defined on all points where one of the input dawgs was defined and
	 * returns the same value as the corresponding dawg.
	 *
	 * @param states
	 *            the set of partial dawgs
	 * @return the union of the sdawg.
	 */
	private DawgState<LETTER, VALUE> union(final Set<DawgState<LETTER, VALUE>> states) {
		// Simple case: singleton set. Union is the single state.
		// This should also catch the final state.
		if (states.size() == 1) {
			return states.iterator().next();
		}
		// Check if we already computed it.
		DawgState<LETTER, VALUE> result = mUnionCache.get(states);
		if (result != null) {
			return result;
		}
		// build the set of successors for each letter.
		Map<Set<DawgState<LETTER, VALUE>>, DawgLetter<LETTER>> newSuccessors = new HashMap<>();
		final Object sort = states.iterator().next().getTransitions().values().iterator().next().getSortId();
		newSuccessors.put(new HashSet<>(), mDawgFactory.getDawgLetterFactory().getUniversalDawgLetter(sort));
		for (final DawgState<LETTER, VALUE> component : states) {
			for (final Map.Entry<DawgState<LETTER, VALUE>, DawgLetter<LETTER>> entry : component.getTransitions()
					.entrySet()) {
				newSuccessors = merge(newSuccessors, entry.getKey(), entry.getValue());
			}
		}
		// build union recursively and build the transition to the union states.
		final Map<DawgState<LETTER, VALUE>, DawgLetter<LETTER>> newTrans = new HashMap<>();
		for (final Map.Entry<Set<DawgState<LETTER, VALUE>>, DawgLetter<LETTER>> entry : newSuccessors.entrySet()) {
			if (!entry.getKey().isEmpty()) {
				final DawgState<LETTER, VALUE> newDest = union(entry.getKey());
				addLetterToMap(newTrans, newDest, entry.getValue());
			}
		}
		result = mDawgStateFactory.createIntermediateState(newTrans);
		mUnionCache.put(states, result);
		return result;
	}

	/**
	 * Build a partial dawg, tha is the reordering of the existing dawg, inserting the remaining columns according to
	 * partialWord.
	 *
	 * @param partialWord
	 *            the letters to insert at the columns which are not in the remap array.
	 * @param offset
	 *            the first column that should be produced for the resulting dawg. Earlier columns will be added by the
	 *            caller.
	 * @param newPositionForColumns
	 *            the remap array, maps from the columns in the original dawg to the columns in the resulting dawg.
	 * @param level
	 *            the current column into the original dawg.
	 * @return the union of the sdawg.
	 */
	private DawgState<LETTER, VALUE> internalReorder(final List<DawgLetter<LETTER>> partialWord, final int offset,
			final int[] newPositionForColumns, final DawgState<LETTER, VALUE> state, final int level) {

		Pair<List<DawgLetter<LETTER>>, DawgState<LETTER, VALUE>> cacheKey = new Pair<>(
				partialWord.subList(offset, partialWord.size()), state);
		DawgState<LETTER, VALUE> result = mCache.get(cacheKey);
		if (result != null) {
			return result;
		}

		if (level == newPositionForColumns.length) {
			result = addLettersInFront(partialWord.subList(offset, partialWord.size()), state);
		} else {
			final int newPosition = newPositionForColumns[level];
			assert newPosition >= offset;
			assert partialWord.get(newPosition) == null;
			int firstNull = offset;
			while (partialWord.get(firstNull) != null) {
				firstNull++;
			}
			if (newPosition == firstNull) {
				// This column is the first still unknown variable, which means we can just recurse with the remaining
				// columns and tell the function not to produce the earlier columns
				final Map<DawgState<LETTER, VALUE>, DawgLetter<LETTER>> newTransition = new HashMap<>();
				for (final Map.Entry<DawgState<LETTER, VALUE>, DawgLetter<LETTER>> entry : state.getTransitions()
						.entrySet()) {
					final DawgState<LETTER, VALUE> newDest = internalReorder(partialWord, newPosition + 1,
							newPositionForColumns, entry.getKey(), level + 1);
					addLetterToMap(newTransition, newDest, entry.getValue());
				}
				result = mDawgStateFactory.createIntermediateState(newTransition);
				result = addLettersInFront(partialWord.subList(offset, newPosition), result);
			} else {
				// This column needs more work.  We recurse with one more letter in partialWord set.
				// In the end we need to union the state.
				final Set<DawgState<LETTER, VALUE>> subsets = new HashSet<>();
				for (final Map.Entry<DawgState<LETTER, VALUE>, DawgLetter<LETTER>> entry : state.getTransitions()
						.entrySet()) {
					partialWord.set(newPosition, entry.getValue());
					subsets.add(internalReorder(partialWord, offset, newPositionForColumns, entry.getKey(), level + 1));
				}
				// clean up partialWord
				partialWord.set(newPosition, null);

				// Now union the subsets recursively.
				result = union(subsets);
			}
		}
		// make sure cacheKey is immutable by copying the partialWord.
		cacheKey = new Pair<>(new ArrayList<>(partialWord.subList(offset, partialWord.size())), state);
		mCache.put(cacheKey, result);
		return result;
	}

	public final DawgState<LETTER, VALUE> reorder(final DawgState<LETTER, VALUE> input,
			final List<DawgLetter<LETTER>> partialWord, final int[] newPositions) {
		return internalReorder(new ArrayList<>(partialWord), 0, newPositions, input, 0);
	}
}
