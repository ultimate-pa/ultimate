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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * Caches computed persistent sets.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters in the persistent sets
 * @param <S>
 *            The type of states for which persistent sets are computed
 */
public class CachedPersistentSetChoice<L, S> implements IPersistentSetChoice<L, S> {
	private final Map<Object, Set<L>> mCache = new HashMap<>();
	private final IPersistentSetChoice<L, S> mUnderlying;
	private final Function<S, Object> mNormalizer;

	/**
	 * Creates a new instance that caches the results of an underlying implementation.
	 *
	 * @param underlying
	 *            The underlying implementation of persistent sets
	 * @param normalizer
	 *            A function mapping a state to some object. States mapped to the same object will get the same
	 *            persistent sets. Set to null if not needed.
	 */
	public CachedPersistentSetChoice(final IPersistentSetChoice<L, S> underlying,
			final Function<S, Object> normalizer) {
		mUnderlying = underlying;
		mNormalizer = normalizer;
	}

	@Override
	public Set<L> persistentSet(final S state) {
		final Object key = normalize(state);

		// Note: Must not be replaced with mCache.computeIfAbsent - need to distinguish between "not cached" and "null".
		if (mCache.containsKey(key)) {
			return mCache.get(key);
		}

		final Set<L> result = mUnderlying.persistentSet(state);
		mCache.put(key, result);
		return result;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mUnderlying.getStatistics();
	}

	@Override
	public boolean ensuresCompatibility(final IDfsOrder<L, S> order) {
		// Note: This is only correct if the normalizing function does not map states with different orders to the same
		// objects.
		return mUnderlying.ensuresCompatibility(order);
	}

	private Object normalize(final S state) {
		if (mNormalizer == null) {
			return state;
		}
		return mNormalizer.apply(state);
	}
}
