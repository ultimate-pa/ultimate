/*
 * Copyright (C) 2024 Emma Bach
 * Copyright (C) 2024 Marcel Ebbinghaus
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ProductPreferenceOrderAutomaton.IProductPreferenceOrderStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class ProductPreferenceOrder<L, S0, S1, S2, S> implements IPreferenceOrder<L, S0, S> {
	private final IPreferenceOrder<L, S0, S1> mFirstOrder;
	private final IPreferenceOrder<L, S0, S2> mSecondOrder;
	private final IProductPreferenceOrderStateFactory<S1, S2, S> mStateFactory;
	private final ProductPreferenceOrderAutomaton<L, S1, S2, S> mAutomaton;

	private final Map<Pair<S0, S>, ProductComparator<L>> mCachedComparators = new HashMap<>();

	public ProductPreferenceOrder(final IPreferenceOrder<L, S0, S1> fst, final IPreferenceOrder<L, S0, S2> snd,
			final IProductPreferenceOrderStateFactory<S1, S2, S> stateFactory) {
		mFirstOrder = fst;
		mSecondOrder = snd;
		mStateFactory = stateFactory;
		mAutomaton = new ProductPreferenceOrderAutomaton<>(mFirstOrder.getMonitor(), mSecondOrder.getMonitor(),
				mStateFactory);
	}

	@Override
	public boolean isPositional() {
		return mFirstOrder.isPositional() || mSecondOrder.isPositional();
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<L, S> getMonitor() {
		return mAutomaton;
	}

	@Override
	public Comparator<L> getOrder(final S0 programState, final S monitorState) {
		final Pair<S0, S> key =
				isPositional() ? new Pair<>(programState, monitorState) : new Pair<>(null, monitorState);
		return mCachedComparators.computeIfAbsent(key, k -> createOrder(k.getFirst(), k.getSecond()));
	}

	private ProductComparator<L> createOrder(final S0 programState, final S monitorState) {
		// This is the hard part.
		// Given Objects a and b that we want to compare, we need to:
		// 1. Check if elements are comparable based on one of the original orders.
		// If not:
		// 1. Find intersection of sets talked about by each order
		// 2. (Ideally) Throw exception if intersection is not a blob
		// 3. Indirectly compare a and b by comparing them to the intersection.

		// Alternatively, we could construct the full transitive closure of the union
		// of mFirstOrder and mSecondOrder, but that seems unnecessarily inefficient.
		return null;
	}

	private static class ProductComparator<L> implements Comparator<L> {
		private final Map<Pair<L, L>, Integer> mComparisonResults = new HashMap<>();

		public ProductComparator(final Comparator<L> lessX, final Comparator<L> lessY, final Set<L> alphabet) {
			// TODO compute transitive closure of union of lessX and lessY, and store it in mComparisonResults
		}

		@Override
		public int compare(final L o1, final L o2) {
			return mComparisonResults.get(new Pair<>(o1, o2));
		}
	}
}
