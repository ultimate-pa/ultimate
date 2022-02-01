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

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;

/**
 * A DawgState is an intermediate state in a Dawg and it basically represents a map from LETTER* to VALUE.
 *
 * @author Alexander Nutz, Jochen Hoenicke
 *
 */
public class DawgState<LETTER, VALUE> {
	final VALUE mFinal;
	/**
	 * The transition map. This looks somehow reverse as it maps from destination state to set of letters. But this
	 * makes it easier to unify transitions going to the same state.
	 */
	final Map<DawgState<LETTER, VALUE>, DawgLetter<LETTER>> mTransitions;

	public DawgState(final VALUE value) {
		mFinal = value;
		mTransitions = null;
	}

	public DawgState(final Map<DawgState<LETTER, VALUE>, DawgLetter<LETTER>> transitions) {
		mFinal = null;
		mTransitions = transitions;
	}

	public boolean isFinal() {
		return mTransitions == null;
	}

	public VALUE getFinalValue() {
		return mFinal;
	}

	@Override
	public String toString() {
		if (isFinal()) {
			return "RET(" + mFinal + ")";
		}
		final StringBuilder sb = new StringBuilder();
		final LinkedHashSet<DawgState<LETTER,VALUE>> toPrint = new LinkedHashSet<>();
		final HashSet<DawgState<LETTER,VALUE>> visited = new HashSet<>();
		toPrint.add(this);
		while (!toPrint.isEmpty()) {
			final DawgState<LETTER,VALUE> state = toPrint.iterator().next();
			toPrint.remove(state);
			if (!visited.add(state)) {
				continue;
			}
			sb.append(String.format("Dawg#%04d", state.hashCode() % 10000));
			String comma ="";
			for (final Map.Entry<DawgState<LETTER, VALUE>, DawgLetter<LETTER>> entry : state.getTransitions()
					.entrySet()) {
				sb.append(comma).append("->");
				if (entry.getKey().isFinal()) {
					sb.append("(").append(entry.getKey().getFinalValue()).append(") ");
				} else {
					sb.append(String.format("#%04d ", entry.getKey().hashCode() % 10000));
					toPrint.add(entry.getKey());
				}
				sb.append(entry.getValue());
				sb.append("\n");
				comma = "         ";
			}
		}
		return sb.toString();
	}

	public Map<DawgState<LETTER, VALUE>, DawgLetter<LETTER>> getTransitions() {
		return mTransitions;
	}

	public VALUE getValue(final List<LETTER> word) {
		DawgState<LETTER, VALUE> state = this;
		for (final LETTER ltr : word) {
			DawgState<LETTER, VALUE> nextState = null;
			for (final Map.Entry<DawgState<LETTER, VALUE>, DawgLetter<LETTER>> trans : state.getTransitions()
					.entrySet()) {
				if (trans.getValue().matches(ltr)) {
					nextState = trans.getKey();
					break;
				}
			}
			state = nextState;
		}
		assert state.isFinal();
		return state.getFinalValue();
	}

	public boolean isTotal() {
		int depth = -1;
		boolean allTotal = true;
		final HashSet<Pair<Integer, DawgState<LETTER, VALUE>>> seen = new HashSet<>();
		final ArrayDeque<Pair<Integer, DawgState<LETTER, VALUE>>> todo = new ArrayDeque<>();
		todo.add(new Pair<>(0, this));
		while (!todo.isEmpty()) {
			final Pair<Integer, DawgState<LETTER, VALUE>> workItem = todo.removeFirst();
			if (!seen.add(workItem)) {
				continue;
			}
			final DawgState<LETTER, VALUE> state = workItem.getSecond();
			if (state.isFinal()) {
				assert depth == -1 || depth == workItem.getFirst();
				depth = workItem.getFirst();
			} else {
				final int newDepth = workItem.getFirst() + 1;
				final DawgLetter<LETTER> first = state.getTransitions().values().iterator().next();
				DawgLetter<LETTER> union = first.intersect(first.complement());
				for (final Entry<DawgState<LETTER, VALUE>, DawgLetter<LETTER>> entry : state.getTransitions()
						.entrySet()) {
					todo.addLast(new Pair<>(newDepth, entry.getKey()));
					assert union.intersect(entry.getValue()).isEmpty();
					union = union.union(entry.getValue());
				}
				allTotal &= union.isUniversal();
			}
		}
		return allTotal;
	}

}
