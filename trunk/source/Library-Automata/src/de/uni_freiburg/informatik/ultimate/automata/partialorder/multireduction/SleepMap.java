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

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
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
	 * @param letter
	 *            The letter labeling the transition
	 * @param lesserLetters
	 *            A map associating all letters less than the given letter with their price
	 * @return A sleep map for the successor state after the given transition.
	 */
	public SleepMap<L, S> computeSuccessor(final S state, final L letter, final Map<L, Integer> lesserLetters,
			final int budget) {
		final Map<L, Integer> successorMap = new HashMap<>();

		// transfer elements of current set
		for (final Map.Entry<L, Integer> entry : mSleepMap.entrySet()) {
			final Integer level = minimumRelation(state, letter, entry.getKey(), entry.getValue());
			if (level != null && level <= budget) {
				successorMap.put(entry.getKey(), level);
			}
		}

		// transfer lesser letters
		for (final Map.Entry<L, Integer> entry : lesserLetters.entrySet()) {
			assert entry.getValue() != null : "Associated price must not be null";
			final Integer oldLevel = successorMap.get(letter);
			final Integer minLevel = oldLevel == null ? entry.getValue() : Integer.min(oldLevel, entry.getValue());
			final Integer level = minimumRelation(state, letter, entry.getKey(), minLevel);
			if (level != null && level <= budget) {
				successorMap.put(entry.getKey(), level);
			}
		}

		return new SleepMap<>(mRelations, successorMap);
	}

	private Integer minimumRelation(final S state, final L a, final L b, final int minLevel) {
		for (int i = minLevel; i < mRelations.size(); i++) {
			if (mRelations.get(i).contains(state, a, b)) {
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