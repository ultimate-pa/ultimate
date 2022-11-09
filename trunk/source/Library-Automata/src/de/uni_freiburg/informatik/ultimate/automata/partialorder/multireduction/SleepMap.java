/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.util.LazyInt;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.CanonicalLatticeForMaps;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IntLattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.UpsideDownLattice;

/**
 * Sleep maps are an extension of sleep sets (from classical partial order reduction algorithms) to multiple
 * independence relations.
 *
 * Like sleep sets, sleep maps contain letters that can be pruned during the exploration of a closed automaton.
 * Additionally, each letter is associated with a "price" corresponding to the index of the maximum independence
 * relation used to justify the presence of the letter in the map.
 *
 * Sleep maps with just one independence relation correspond exactly to sleep sets.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters in the sleep map
 * @param <S>
 *            The type of states used for conditional independence
 */
public final class SleepMap<L, S> {
	private final List<IIndependenceRelation<S, L>> mRelations;
	private final Map<L, Integer> mSleepMap;
	private final LazyInt mHash;

	private SleepMap(final List<IIndependenceRelation<S, L>> relations, final Map<L, Integer> sleepMap) {
		assert !relations.isEmpty() : "Sleep maps must have at least one independence relation.";
		mRelations = relations;
		mSleepMap = sleepMap;
		mHash = new LazyInt(mSleepMap::hashCode);
	}

	/**
	 * Determines if a given letter is in the sleep map and can hence be pruned.
	 *
	 * @param letter
	 *            The letter for which membership is checked
	 * @return true if the given letter is in the map
	 */
	public boolean contains(final L letter) {
		return mSleepMap.containsKey(letter);
	}

	/**
	 * For a letter in the map, determines the associated price.
	 *
	 * @param letter
	 *            A letter for which {@link #contains(L)} returns true
	 * @return the associated price
	 *
	 * @throws UnsupportedOperationException
	 *             if the given letter is not in the map
	 */
	public int getPrice(final L letter) {
		if (contains(letter)) {
			return mSleepMap.get(letter);
		}
		throw new UnsupportedOperationException();
	}

	@Override
	public int hashCode() {
		return mHash.get();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || getClass() != obj.getClass()) {
			return false;
		}
		final SleepMap<?, ?> other = (SleepMap<?, ?>) obj;
		return ((Object) mRelations) == other.mRelations && Objects.equals(mSleepMap, other.mSleepMap);
	}

	/**
	 * Computes the successor sleep map after a transition.
	 *
	 * @param state
	 *            The source state of the transition
	 * @param transitionLetter
	 *            The letter labeling the transition
	 * @param lesserLetters
	 *            A map associating all letters less than the given letter with their price
	 * @param budget
	 *            The budget for the successor state, i.e., the index of the maximal independence relation that can be
	 *            used from the successor state on.
	 * @return A sleep map for the successor state after the given transition.
	 */
	public SleepMap<L, S> computeSuccessor(final S state, final L transitionLetter, final Map<L, Integer> lesserLetters,
			final int budget) {
		final Map<L, Integer> successorMap = new HashMap<>();

		for (final var entry : mSleepMap.entrySet()) {
			final L currentLetter = entry.getKey();
			assert !successorMap.containsKey(currentLetter) : "budget should not be computed twice";

			// Compute the "cost" of currentLetter:
			// The minimum of its budget at the current state (but only if it is ordered before transitionLetter)
			// and its price in the old sleep map.
			final Integer freshPrice = lesserLetters.get(currentLetter);
			final int cost = freshPrice == null ? entry.getValue() : Integer.min(freshPrice, entry.getValue());

			// "Transfer" the currentLetter across the transition labeled with "transitionLetter":
			// Increase the price to a relation where the two letters are independent (if such a relation exists).
			final Integer transferred = minimumRelation(state, transitionLetter, currentLetter, cost, budget);
			if (transferred != null) {
				// Check that the price is "constrained": It must not exceed the budget.
				// The method #minimumRelation already ensures this.
				assert transferred <= budget : "computed price is not constrained by budget";

				// Enter the letter with the computed price in the new sleep map.
				successorMap.put(currentLetter, transferred);
			}
		}

		for (final var entry : lesserLetters.entrySet()) {
			final L currentLetter = entry.getKey();
			if (mSleepMap.containsKey(currentLetter)) {
				// already dealt with in the loop above
				continue;
			}
			assert !successorMap.containsKey(currentLetter) : "budget should not be computed twice";

			// Compute the "cost" of currentLetter: Its budget at the current state.
			// (Because of the conditional above, we know the letter is not in the old sleep map.)
			assert !mSleepMap.containsKey(currentLetter);
			final int cost = entry.getValue();

			// "Transfer" the currentLetter across the transition labeled with "transitionLetter":
			// Increase the price to a relation where the two letters are independent (if such a relation exists).
			final Integer transferred = minimumRelation(state, transitionLetter, currentLetter, cost, budget);
			if (transferred != null) {
				// Check that the price is "constrained": It must not exceed the budget.
				// The method #minimumRelation already ensures this.
				assert transferred <= budget : "computed price is not constrained by budget";

				// Enter the letter with the computed price in the new sleep map.
				successorMap.put(currentLetter, transferred);
			}
		}

		return new SleepMap<>(mRelations, Map.copyOf(successorMap));
	}

	private Integer minimumRelation(final S state, final L a, final L b, final int minLevel, final int maxLevel) {
		for (int i = minLevel; i <= maxLevel; i++) {
			if (mRelations.get(i).isIndependent(state, a, b) == Dependence.INDEPENDENT) {
				return i;
			}
		}
		return null;
	}

	/**
	 * Creates an empty sleep map.
	 *
	 * @param <L>
	 *            The type of letters in the map
	 * @param <S>
	 *            The type of states used for conditional independence
	 *
	 * @param relations
	 *            The sequence of relations used for Partial Order Reduction
	 * @return An empty sleep map
	 */
	public static <L, S> SleepMap<L, S> empty(final List<IIndependenceRelation<S, L>> relations) {
		return new SleepMap<>(relations, Collections.emptyMap());
	}

	/**
	 * Implements comparison of sleep maps. Sleep maps based on the same sequence of independence relations form a
	 * lattice w.r.t. to this order relation. Infimum and supremum operations are implemented below.
	 *
	 * For sleep sets (i.e., sleep maps with just one independence relation), this order corresponds to set inclusion.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 *            The type of letters in the sleep maps
	 * @param <S>
	 *            The type of states used by the sleep maps
	 */
	public static final class Lattice<L, S> implements ILattice<SleepMap<L, S>> {
		private final List<IIndependenceRelation<S, L>> mRelations;
		private final ILattice<Map<L, Integer>> mMapLattice =
				new CanonicalLatticeForMaps<>(new UpsideDownLattice<>(new IntLattice()));

		public Lattice(final List<IIndependenceRelation<S, L>> relations) {
			mRelations = relations;
		}

		@Override
		public ComparisonResult compare(final SleepMap<L, S> o1, final SleepMap<L, S> o2) {
			if (o1.mRelations != mRelations || o2.mRelations != mRelations) {
				throw new IllegalArgumentException("Cannot compare maps with different relations");
			}
			return mMapLattice.compare(o1.mSleepMap, o2.mSleepMap);
		}

		@Override
		public SleepMap<L, S> infimum(final SleepMap<L, S> m1, final SleepMap<L, S> m2) {
			if (m1.mRelations != mRelations || m2.mRelations != mRelations) {
				throw new IllegalArgumentException("Cannot compute infimum for maps with different relations");
			}
			return new SleepMap<>(m1.mRelations, mMapLattice.infimum(m1.mSleepMap, m2.mSleepMap));
		}

		@Override
		public SleepMap<L, S> supremum(final SleepMap<L, S> m1, final SleepMap<L, S> m2) {
			if (m1.mRelations != mRelations || m2.mRelations != mRelations) {
				throw new IllegalArgumentException("Cannot compute supremum for maps with different relations");
			}
			return new SleepMap<>(m1.mRelations, mMapLattice.supremum(m1.mSleepMap, m2.mSleepMap));
		}

		@Override
		public SleepMap<L, S> getBottom() {
			return SleepMap.empty(mRelations);
		}

		@Override
		public SleepMap<L, S> getTop() {
			// TODO map all letters to 0
			throw new UnsupportedOperationException();
		}
	}
}
