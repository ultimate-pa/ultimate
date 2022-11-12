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
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;

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

	private final CacheStatistics mStatistics = new CacheStatistics();
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
		return mStatistics;
	}

	private final class CacheStatistics extends AbstractStatisticsDataProvider {
		public static final String TOTAL_CACHE_SIZE = "Total cache size (in pairs)";
		public static final String POSITIVE_CACHE_SIZE = "Positive cache size";
		public static final String POSITIVE_CONDITIONAL_CACHE_SIZE = "Positive conditional cache size";
		public static final String POSITIVE_UNCONDITIONAL_CACHE_SIZE = "Positive unconditional cache size";
		public static final String NEGATIVE_CACHE_SIZE = "Negative cache size";
		public static final String NEGATIVE_CONDITIONAL_CACHE_SIZE = "Negative conditional cache size";
		public static final String NEGATIVE_UNCONDITIONAL_CACHE_SIZE = "Negative unconditional cache size";
		public static final String UNKNOWN_CACHE_SIZE = "Unknown cache size";
		public static final String UNKNOWN_CONDITIONAL_CACHE_SIZE = "Unknown conditional cache size";
		public static final String UNKNOWN_UNCONDITIONAL_CACHE_SIZE = "Unknown unconditional cache size";

		private CacheStatistics() {
			declare(TOTAL_CACHE_SIZE, this::getTotalSize, KeyType.COUNTER);
			declare(POSITIVE_CACHE_SIZE, this::getPositiveCacheSize, KeyType.COUNTER);
			declare(POSITIVE_CONDITIONAL_CACHE_SIZE, this::getPositiveConditionalCacheSize, KeyType.COUNTER);
			declare(POSITIVE_UNCONDITIONAL_CACHE_SIZE, this::getPositiveUnconditionalCacheSize, KeyType.COUNTER);
			declare(NEGATIVE_CACHE_SIZE, this::getNegativeCacheSize, KeyType.COUNTER);
			declare(NEGATIVE_CONDITIONAL_CACHE_SIZE, this::getNegativeConditionalCacheSize, KeyType.COUNTER);
			declare(NEGATIVE_UNCONDITIONAL_CACHE_SIZE, this::getNegativeUnconditionalCacheSize, KeyType.COUNTER);
			declare(UNKNOWN_CACHE_SIZE, this::getUnknownCacheSize, KeyType.COUNTER);
			declare(UNKNOWN_CONDITIONAL_CACHE_SIZE, this::getUnknownConditionalCacheSize, KeyType.COUNTER);
			declare(UNKNOWN_UNCONDITIONAL_CACHE_SIZE, this::getUnknownUnconditionalCacheSize, KeyType.COUNTER);
		}

		public int getTotalSize() {
			return getPositiveCacheSize() + getNegativeCacheSize();
		}

		public int getPositiveCacheSize() {
			return getCacheSize(mIndependentCache);
		}

		public int getPositiveConditionalCacheSize() {
			return getPositiveCacheSize() - getPositiveUnconditionalCacheSize();
		}

		public int getPositiveUnconditionalCacheSize() {
			return getUnconditionalCacheSize(mIndependentCache);
		}

		public int getNegativeCacheSize() {
			return getCacheSize(mDependentCache);
		}

		public int getNegativeConditionalCacheSize() {
			return getNegativeCacheSize() - getNegativeUnconditionalCacheSize();
		}

		public int getNegativeUnconditionalCacheSize() {
			return getUnconditionalCacheSize(mDependentCache);
		}

		public int getUnknownCacheSize() {
			return getCacheSize(mUnknownCache);
		}

		public int getUnknownConditionalCacheSize() {
			return getUnknownCacheSize() - getUnknownUnconditionalCacheSize();
		}

		public int getUnknownUnconditionalCacheSize() {
			return getUnconditionalCacheSize(mUnknownCache);
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
	}
}
