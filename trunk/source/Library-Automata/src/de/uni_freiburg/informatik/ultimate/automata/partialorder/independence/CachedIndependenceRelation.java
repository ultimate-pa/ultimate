/*
 * Copyright (C) 2019 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IndependenceResultAggregator.Counter;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * An independence relation that caches the result of an underlying relation. To be used with computation-intensive
 * independence relations.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <S>
 *            If the relation is conditional, the type of states serving as conditions. Use a wildcard for unconditional
 *            relations.
 * @param <L>
 *            The type of letters whose independence is defined by the relation.
 */
public class CachedIndependenceRelation<S, L> implements IIndependenceRelation<S, L> {

	private final IIndependenceRelation<S, L> mUnderlying;
	private final IIndependenceCache<S, L> mCache;
	private final CachedIndependenceStatisticsProvider mStatistics;

	/**
	 * Create a new cache for the given relation.
	 *
	 * @param underlying
	 *            The underlying relation that will be queried and whose results will be cached.
	 */
	public CachedIndependenceRelation(final IIndependenceRelation<S, L> underlying) {
		this(underlying, new DefaultIndependenceCache<>());
	}

	/**
	 * Create a new cache for the given relation.
	 *
	 * @param underlying
	 *            The underlying relation that will be queried and whose results will be cached.
	 * @param cache
	 *            A cache object used to retrieve and store independence. This parameter allows re-use and sharing of
	 *            cached information across instances. Use with care as it allows potentially unsound mixing of
	 *            different relations through a shared cache.
	 */
	public CachedIndependenceRelation(final IIndependenceRelation<S, L> underlying,
			final IIndependenceCache<S, L> cache) {
		mUnderlying = underlying;
		mCache = cache;
		mStatistics = new CachedIndependenceStatisticsProvider();
	}

	/**
	 * @return The cache instance used to store and retrieve independence information.
	 */
	public IIndependenceCache<S, L> getCache() {
		return mCache;
	}

	@Override
	public boolean isSymmetric() {
		return mUnderlying.isSymmetric();
	}

	@Override
	public boolean isConditional() {
		return mUnderlying.isConditional();
	}

	@Override
	public Dependence isIndependent(final S state, final L a, final L b) {
		final S condition = isConditional() ? state : null;

		final Dependence cached = mCache.contains(condition, a, b);
		if (cached != null) {
			mStatistics.reportCachedQuery(cached, condition != null);
			return cached;
		}

		if (isSymmetric()) {
			final Dependence symCached = mCache.contains(condition, b, a);
			if (symCached != null) {
				mStatistics.reportCachedQuery(symCached, condition != null);
				return symCached;
			}
		}

		final Dependence result = mUnderlying.isIndependent(condition, a, b);
		mCache.cacheResult(condition, a, b, result);
		mStatistics.reportUncachedQuery(result, condition != null);
		return result;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	/**
	 * Purge all information involving a given letter from the cache.
	 *
	 * @param a
	 *            The letter whose independencies and dependencies shall be removed.
	 */
	public void removeFromCache(final L a) {
		mCache.remove(a);
	}

	private final class CachedIndependenceStatisticsProvider extends IndependenceStatisticsDataProvider {
		public static final String CACHE_QUERIES = "Cache Queries";
		public static final String CACHE_STATISTICS = "Statistics on independence cache";

		private final Counter mCacheQueries = new Counter();

		private CachedIndependenceStatisticsProvider() {
			super(CachedIndependenceRelation.class, mUnderlying);
			declareCounter(CACHE_QUERIES, () -> mCacheQueries);
			forward(CACHE_STATISTICS, mCache::getStatistics);
		}

		private void reportCachedQuery(final Dependence result, final boolean conditional) {
			reportQuery(result, conditional);
			mCacheQueries.increment(result, conditional);
		}

		private void reportUncachedQuery(final Dependence result, final boolean conditional) {
			reportQuery(result, conditional);
			mCacheQueries.increment(Dependence.UNKNOWN, conditional);
		}
	}

	/**
	 * A cache used to store independence information.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <S>
	 *            The type of conditions (arbitrary in case of non-conditional independence)
	 * @param <L>
	 *            The type of letters
	 */
	public interface IIndependenceCache<S, L> {
		/**
		 * Determine if the cache contains certain independence information.
		 *
		 * @param condition
		 *            A condition in case of conditional independence, null otherwise.
		 * @param a
		 *            The first letter
		 * @param b
		 *            The second letter
		 * @return The cached result of an independence check, or {@code null} if no result has been cached.
		 */
		Dependence contains(S condition, L a, L b);

		/**
		 * Remove all independence and dependence information involving a given letter.
		 *
		 * @param a
		 *            The letter whose information shall be removed.
		 */
		void remove(L a);

		/**
		 * Add information to the cache.
		 *
		 * @param condition
		 *            A condition, or null in case of non-conditional independence.
		 * @param a
		 *            The first letter
		 * @param b
		 *            The second letter
		 * @param result
		 *            The result of an independence check
		 */
		void cacheResult(S condition, L a, L b, Dependence result);

		/**
		 * Merges cached independencies for two letters into a combined letter. If both are independent from some third
		 * letter c, the combined letter will be independent from c as well.
		 *
		 * This method can be used to transfer knowledge about letters to a (sequential or choice) composition of these
		 * letters. The caller must ensure soundness, it is not checked against the underlying relation (as this would
		 * defeat the purpose).
		 *
		 * @param a
		 *            The first letter
		 * @param b
		 *            The second letter
		 * @param ab
		 *            The combination (e.g. sequential composition) of the previous two letters.
		 */
		void mergeIndependencies(L a, L b, L ab);

		/**
		 * An optional method to provide statistics about the cache.
		 *
		 * @return implementation-defined statistics
		 */
		default IStatisticsDataProvider getStatistics() {
			return new AbstractStatisticsDataProvider() {
				// by default, no statistics are collected
			};
		}
	}
}
