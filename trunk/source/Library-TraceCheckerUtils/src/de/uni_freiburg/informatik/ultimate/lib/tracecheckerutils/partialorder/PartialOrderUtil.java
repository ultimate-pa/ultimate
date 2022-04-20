/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;

public final class PartialOrderUtil {
	private PartialOrderUtil() {
	}

	// Useful for debugging. Not optimized at all, might only work in limited cases.
	public static <L, S> Word<L> computeRepresentative(final Word<L> word, final Class<L> clazz,
			final INwaOutgoingLetterAndTransitionProvider<L, S> automaton,
			final IIndependenceRelation<S, L> independence, final IDfsOrder<L, S> order) {
		final List<L> pref = new ArrayList<>(word.length());
		final List<L> suff = new ArrayList<>(word.asList());
		S state = automaton.getInitialStates().iterator().next();
		while (!suff.isEmpty()) {
			final List<OutgoingInternalTransition<L, S>> worklist = new ArrayList<>();
			automaton.internalSuccessors(state).forEach(worklist::add);
			worklist.sort(Comparator.comparing(OutgoingInternalTransition::getLetter, order.getOrder(state)));
			final int sizeBefore = suff.size();
			for (final OutgoingInternalTransition<L, S> t : worklist) {
				final L x = t.getLetter();
				final int index = suff.indexOf(x);
				if (index == -1) {
					continue;
				}
				boolean isNext = true;
				for (int i = 0; i < index; ++i) {
					if (!independence.contains(null, suff.get(i), x)) {
						isNext = false;
						break;
					}
				}
				if (!isNext) {
					continue;
				}
				pref.add(x);
				suff.remove(index);
				state = t.getSucc();
				break;
			}
			assert suff.size() == sizeBefore - 1 : "size must decrease in every iteration";
		}

		return new Word<>(pref.toArray(i -> (L[]) Array.newInstance(clazz, i)));
	}
}
