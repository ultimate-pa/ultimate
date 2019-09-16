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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates;

import java.util.Collections;
import java.util.Iterator;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.BinaryMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ArrayMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnifyHash;

/**
 *
 * Manages DawgStates
 * <li>creates fresh states
 * <li>creates and manages PairDawgStates (keeps them unique)
 *
 * @author Alexander Nutz, Jochen Hoenicke
 */
public class DawgStateFactory<LETTER> {
	final UnifyHash<DawgState<LETTER, ?>> mExistingStates = new UnifyHash<>();

	@SuppressWarnings("unchecked")
	public <VALUE> DawgState<LETTER, VALUE> createFinalState(final VALUE value) {
		final int hash = value == null ? 0 : value.hashCode();
		for (final DawgState<LETTER, ?> previous : mExistingStates.iterateHashCode(hash)) {
			if (previous.isFinal()
					&& previous.getFinalValue() == null ? value == null : previous.getFinalValue().equals(value)) {
				return (DawgState<LETTER, VALUE>) previous;
			}
		}
		final DawgState<LETTER, VALUE> result = new DawgState<>(value);
		mExistingStates.put(hash, result);
		// assert result.checkState();
		return result;
	}

	@SuppressWarnings("unchecked")
	public <VALUE> DawgState<LETTER, VALUE>
			createIntermediateState(Map<DawgState<LETTER, VALUE>, DawgLetter<LETTER>> transitions) {
		final int hash = transitions.hashCode();
		for (final DawgState<LETTER, ?> previous : mExistingStates.iterateHashCode(hash)) {
			if (previous.mTransitions.equals(transitions)) {
				return (DawgState<LETTER, VALUE>) previous;
			}
		}
		if (transitions.size() == 0) {
			transitions = Collections.emptyMap();
		} else if (transitions.size() == 1) {
			final Map.Entry<DawgState<LETTER, VALUE>, DawgLetter<LETTER>> entry = transitions.entrySet().iterator().next();
			transitions = Collections.singletonMap(entry.getKey(), entry.getValue());
		} else if (!(transitions instanceof BinaryMap) && !(transitions instanceof ArrayMap)) {
			if (transitions.size() == 2) {
				final Iterator<Map.Entry<DawgState<LETTER, VALUE>, DawgLetter<LETTER>>> it = transitions.entrySet().iterator();
				final Map.Entry<DawgState<LETTER, VALUE>, DawgLetter<LETTER>> entry1 = it .next();
				final Map.Entry<DawgState<LETTER, VALUE>, DawgLetter<LETTER>> entry2 = it.next();
				transitions = new BinaryMap<>(entry1.getKey(), entry1.getValue(), entry2.getKey(), entry2.getValue());
			} else {
				final Map.Entry<DawgState<LETTER, VALUE>, DawgLetter<LETTER>>[] entries =
						transitions.entrySet().toArray((Map.Entry<DawgState<LETTER, VALUE>, DawgLetter<LETTER>>[])
								new Map.Entry[transitions.size()]);
				final DawgState<LETTER, VALUE>[] keys = new DawgState[entries.length];
				final DawgLetter<LETTER>[] values = new DawgLetter[entries.length];
				for (int i = 0; i < entries.length; i++) {
					keys[i] = entries[i].getKey();
					values[i] = entries[i].getValue();
				}
				transitions = new ArrayMap<>(keys, values);
			}
		}
		final DawgState<LETTER, VALUE> result = new DawgState<>(transitions);
		mExistingStates.put(hash, result);
		// assert result.isTotal() || true;
		return result;
	}
}
