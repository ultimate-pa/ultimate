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
package de.uni_freiburg.informatik.ultimate.automata.partialorder.independence;

import java.util.HashMap;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.CachedIndependenceRelation.IIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * Default implementation of {@link IIndependenceCache}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <S>
 *            The type of conditions (arbitrary in case of non-conditional independence)
 * @param <L>
 *            The type of letters
 */
public class DefaultIndependenceCache<S, L> implements IIndependenceCache<S, L> {
	private final Map<S, HashRelation<L, L>> mIndependentCache = new HashMap<>();
	private final Map<S, HashRelation<L, L>> mDependentCache = new HashMap<>();
	private final Map<S, HashRelation<L, L>> mUnknownCache = new HashMap<>();

	@Override
	public Dependence contains(final S condition, final L a, final L b) {
		if (condition != null) {
			// For conditional queries, check unconditional independence first.
			final HashRelation<L, L> globalPositive = mIndependentCache.get(null);
			if (globalPositive != null && globalPositive.containsPair(a, b)) {
				return Dependence.INDEPENDENT;
			}
		}

		final HashRelation<L, L> positive = mIndependentCache.get(condition);
		if (positive != null && positive.containsPair(a, b)) {
			return Dependence.INDEPENDENT;
		}

		final HashRelation<L, L> negative = mDependentCache.get(condition);
		if (negative != null && negative.containsPair(a, b)) {
			return Dependence.DEPENDENT;
		}

		final HashRelation<L, L> unknown = mUnknownCache.get(condition);
		if (unknown != null && unknown.containsPair(a, b)) {
			return Dependence.UNKNOWN;
		}

		return null;
	}

	@Override
	public void remove(final L a) {
		removeFromCache(mIndependentCache, a);
		removeFromCache(mDependentCache, a);
		removeFromCache(mUnknownCache, a);
	}

	private void removeFromCache(final Map<?, HashRelation<L, L>> cache, final L elem) {
		final var it = cache.values().iterator();
		while (it.hasNext()) {
			final var relation = it.next();
			relation.removeDomainElement(elem);
			relation.removeRangeElement(elem);
			if (relation.isEmpty()) {
				it.remove();
			}
		}
	}

	/**
	 * Remove all information about conditional independence from this cache, but keep unconditional independence
	 * information.
	 */
	public void clearConditional() {
		clearConditional(mIndependentCache);
		clearConditional(mDependentCache);
		clearConditional(mUnknownCache);
	}

	private void clearConditional(final Map<S, HashRelation<L, L>> cache) {
		final var unconditional = cache.get(null);
		cache.clear();
		if (unconditional != null) {
			cache.put(null, unconditional);
		}
	}

	@Override
	public void cacheResult(final S condition, final L a, final L b, final Dependence result) {
		final Map<S, HashRelation<L, L>> cache = getCache(result);
		final HashRelation<L, L> row = cache.computeIfAbsent(condition, x -> new HashRelation<>());
		row.addPair(a, b);
	}

	private Map<S, HashRelation<L, L>> getCache(final Dependence result) {
		switch (result) {
		case DEPENDENT:
			return mDependentCache;
		case INDEPENDENT:
			return mIndependentCache;
		case UNKNOWN:
			return mUnknownCache;
		}
		throw new IllegalArgumentException();
	}

	@Override
	public void mergeIndependencies(final L a, final L b, final L ab) {
		for (final HashRelation<L, L> relation : mIndependentCache.values()) {
			// (a, c) + (b, c) -> (ab, c)
			for (final L c : relation.getImage(a)) {
				if (relation.containsPair(b, c)) {
					relation.addPair(ab, c);
				}
			}
			// (c, a) + (c, b) -> (c, ab)
			for (final L c : relation.getDomain()) {
				if (relation.containsPair(c, a) && relation.containsPair(c, b)) {
					relation.addPair(c, ab);
				}
			}
		}
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return new CacheStatistics();
	}

	private final class CacheStatistics extends AbstractStatisticsDataProvider {
		public static final String TOTAL_CACHE_SIZE = "Total cache size (in pairs)";

		private CacheStatistics() {
			declareCounter(TOTAL_CACHE_SIZE, this::getTotalSize);
			declareCacheStatistics("Positive", mIndependentCache);
			declareCacheStatistics("Negative", mDependentCache);
			declareCacheStatistics("Unknown", mUnknownCache);
		}

		private void declareCacheStatistics(final String name, final Map<S, HashRelation<L, L>> cache) {
			declareCounter(name + " cache size", () -> getCacheSize(cache));
			declareCounter(name + " conditional cache size", () -> getConditionalCacheSize(cache));
			declareCounter(name + " unconditional cache size", () -> getUnconditionalCacheSize(cache));
		}

		private int getTotalSize() {
			return getCacheSize(mIndependentCache) + getCacheSize(mDependentCache) + getCacheSize(mUnknownCache);
		}

		private int getCacheSize(final Map<S, HashRelation<L, L>> cache) {
			return cache.entrySet().stream().collect(Collectors.summingInt(e -> e.getValue().size()));
		}

		private int getUnconditionalCacheSize(final Map<S, HashRelation<L, L>> cache) {
			final HashRelation<L, L> row = cache.get(null);
			if (row == null) {
				return 0;
			}
			return row.size();
		}

		private int getConditionalCacheSize(final Map<S, HashRelation<L, L>> cache) {
			return getCacheSize(cache) - getUnconditionalCacheSize(cache);
		}
	}
}
