/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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

import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgStateFactory;

/**
 * This creates a new Dawg where some columns are existentially quantified. This means that
 * {@code evaluate(newdawg, word)} holds if and only if there is an extension of the word for the removed columns to
 * some word', such that {@code evaluate(olddawg, word)} holds.
 *
 * @author Jochen Hoenicke
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class ProjectDawgBuilder<LETTER, COLNAMES> extends DawgBuilder<LETTER> {
	private final DawgStateFactory<LETTER> mDawgStateFactory;
	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;
	private final Map<Set<DawgState<LETTER, Boolean>>, DawgState<LETTER, Boolean>> mCache;
	private final int mNumColumns;
	private final BitSet mProjectedColumns;

	public ProjectDawgBuilder(final DawgFactory<LETTER, COLNAMES> factory, final int numColumns, final BitSet projected) {
		mDawgFactory = factory;
		mDawgStateFactory = mDawgFactory.getDawgStateFactory();
		mNumColumns = numColumns;
		mProjectedColumns = projected;
		mCache = new HashMap<>();
	}

	private DawgState<LETTER, Boolean> projectAndJoin(final Set<DawgState<LETTER, Boolean>> suffixes, final int level) {
		DawgState<LETTER, Boolean> result = mCache.get(suffixes);
		if (result != null) {
			return result;
		}
		if (level == mNumColumns) {
			// Check if there is a true node and return it.
			for (final DawgState<LETTER, Boolean> component : suffixes) {
				assert component.isFinal();
				if (component.getFinalValue()) {
					return component;
				}
			}
			// No true node, so there must be a false node (since the dags are complete).
			assert !suffixes.isEmpty();
			result = suffixes.iterator().next();
		} else if (mProjectedColumns.get(level)) {
			// This column should appear.  Compute the new set for each input separately.  We may need to split here.
			Map<Set<DawgState<LETTER, Boolean>>, DawgLetter<LETTER>> newSuccessors = new HashMap<>();
			final Object sort = suffixes.iterator().next().getTransitions().values().iterator().next().getSortId();
			newSuccessors.put(new HashSet<>(), mDawgFactory.getDawgLetterFactory().getUniversalDawgLetter(sort));
			for (final DawgState<LETTER, Boolean> component : suffixes) {
				for (final Map.Entry<DawgState<LETTER, Boolean>, DawgLetter<LETTER>> entry
						: component.getTransitions().entrySet()) {
					newSuccessors = merge(newSuccessors, entry.getKey(), entry.getValue());
				}
			}
			final Map<DawgState<LETTER, Boolean>, DawgLetter<LETTER>> newTrans = new HashMap<>();
			for (final Map.Entry<Set<DawgState<LETTER, Boolean>>, DawgLetter<LETTER>> entry : newSuccessors
					.entrySet()) {
				final DawgState<LETTER, Boolean> newDest = projectAndJoin(entry.getKey(), level + 1);
				addLetterToMap(newTrans, newDest, entry.getValue());
			}
			result = mDawgStateFactory.createIntermediateState(newTrans);
		} else {
			// This column is projected away. Basically we merge all sets.
			final Set<DawgState<LETTER, Boolean>> newReachableStates = new HashSet<>();
			for (final DawgState<LETTER, Boolean> component : suffixes) {
				newReachableStates.addAll(component.getTransitions().keySet());
			}
			result = projectAndJoin(newReachableStates, level + 1);
		}
		mCache.put(suffixes, result);
		return result;
	}

	public final DawgState<LETTER, Boolean> project(final DawgState<LETTER, Boolean> input) {
		return projectAndJoin(Collections.singleton(input), 0);
	}
}
