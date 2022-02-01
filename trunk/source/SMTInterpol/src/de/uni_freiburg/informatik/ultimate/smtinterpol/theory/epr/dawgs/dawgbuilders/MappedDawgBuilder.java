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
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgStateFactory;

/**
 * Class to Map a the values stored in a Dawg. It creates an equivalent structure just with different values at the end.
 *
 * @author Alexander Nutz, Jochen Hoenicke
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class MappedDawgBuilder<LETTER, COLNAMES, V1, V2> extends DawgBuilder<LETTER> {
	private final DawgStateFactory<LETTER> mDawgStateFactory;
	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;
	private final Function<V1, V2> mOperation;
	private final Map<DawgState<LETTER, V1>, DawgState<LETTER, V2>> mCache;

	public MappedDawgBuilder(final DawgFactory<LETTER, COLNAMES> factory, final Function<V1, V2> operation) {
		mDawgFactory = factory;
		mDawgStateFactory = mDawgFactory.getDawgStateFactory();
		mOperation = operation;
		mCache = new HashMap<>();
	}

	public DawgState<LETTER, V2> map(final DawgState<LETTER, V1> input) {
		DawgState<LETTER, V2> result = mCache.get(input);
		if (result != null) {
			return result;
		}
		if (input.isFinal()) {
			result = mDawgStateFactory.createFinalState(mOperation.apply(input.getFinalValue()));
		} else {
			final HashMap<DawgState<LETTER, V2>, DawgLetter<LETTER>> newTrans = new HashMap<>();
			for (final Map.Entry<DawgState<LETTER, V1>, DawgLetter<LETTER>> trans : input.getTransitions().entrySet()) {
				addLetterToMap(newTrans, map(trans.getKey()), trans.getValue());
			}
			result = mDawgStateFactory.createIntermediateState(newTrans);
		}
		mCache.put(input, result);
		return result;
	}
}