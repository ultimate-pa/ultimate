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

import java.util.HashMap;
import java.util.Map;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgStateFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class ProductDawgBuilder<LETTER, COLNAMES, V1, V2, V3> {
	private final DawgStateFactory<LETTER> mDawgStateFactory;
	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;
	private final BiFunction<V1, V2, V3> mOperation;
	private final Map<Pair<DawgState<LETTER, V1>, DawgState<LETTER, V2>>, DawgState<LETTER, V3>> mCache;

	public ProductDawgBuilder(final DawgFactory<LETTER, COLNAMES> factory, final BiFunction<V1, V2, V3> operation) {
		mDawgFactory = factory;
		mDawgStateFactory = mDawgFactory.getDawgStateFactory();
		mOperation = operation;
		mCache = new HashMap<>();
	}

	public DawgState<LETTER, V3> product(final DawgState<LETTER, V1> state1, final DawgState<LETTER, V2> state2) {
		final Pair<DawgState<LETTER, V1>, DawgState<LETTER, V2>> input = new Pair<>(state1, state2);
		DawgState<LETTER, V3> result = mCache.get(input);
		if (result != null) {
			return result;
		}
		if (state1.isFinal()) {
			assert state2.isFinal();
			result = mDawgStateFactory.createFinalState(mOperation.apply(state1.getFinalValue(), state2.getFinalValue()));
		} else {
			final HashMap<DawgState<LETTER,V3>, DawgLetter<LETTER>> newTrans = new HashMap<>();
			for (final Map.Entry<DawgState<LETTER, V1>, DawgLetter<LETTER>> trans1 : state1.getTransitions().entrySet()) {
				for (final Map.Entry<DawgState<LETTER, V2>, DawgLetter<LETTER>> trans2 : state2.getTransitions().entrySet()) {
					if (!trans1.getValue().isDisjoint(trans2.getValue())) {
						final DawgLetter<LETTER> newLetter = trans1.getValue().intersect(trans2.getValue());
						final DawgState<LETTER, V3> newState = product(trans1.getKey(), trans2.getKey());
						if (newTrans.containsKey(newState)) {
							newTrans.put(newState, newTrans.get(newState).union(newLetter));
						} else {
							newTrans.put(newState, newLetter);
						}
					}
				}
			}
			result = mDawgStateFactory.createIntermediateState(newTrans);
		}
		mCache.put(input, result);
		return result;
	}
}