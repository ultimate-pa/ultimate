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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.HashMap;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

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
	private final Cache<S, L> mCache;

	/**
	 * Create a new cache for the given relation.
	 *
	 * @param underlying
	 *            The underlying relation that will be queried and whose results will be cached.
	 */
	public CachedIndependenceRelation(final IIndependenceRelation<S, L> underlying) {
		this(underlying, new Cache<>(null));
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
	public CachedIndependenceRelation(final IIndependenceRelation<S, L> underlying, final Cache<S, L> cache) {
		mUnderlying = underlying;
		mCache = cache;
	}

	/**
	 * @return The cache instance used to store and retrieve independence information.
	 */
	public Cache<S, L> getCache() {
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
	public boolean contains(final S state, final L a, final L b) {
		final S condition = isConditional() ? state : null;

		final LBool cached = mCache.contains(condition, a, b);
		if (cached == LBool.SAT) {
			return true;
		} else if (cached == LBool.UNSAT) {
			return false;
		}

		if (isSymmetric()) {
			final LBool symCached = mCache.contains(condition, b, a);
			if (symCached == LBool.SAT) {
				return true;
			} else if (symCached == LBool.UNSAT) {
				return false;
			}
		}

		final boolean result = mUnderlying.contains(condition, a, b);
		mCache.cacheResult(condition, a, b, result);
		return result;
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
	public static class Cache<S, L> {
		private final Map<Object, HashRelation<L, L>> mPositiveCache = new HashMap<>();
		private final Map<Object, HashRelation<L, L>> mNegativeCache = new HashMap<>();
		private final IConditionNormalizer<S, L> mNormalizer;

		/**
		 * Create a cache.
		 *
		 * @param normalizer
		 *            Can be used to improve caching efficiency. See {@link IConditionNormalizer} for details.
		 */
		public Cache(final IConditionNormalizer<S, L> normalizer) {
			mNormalizer = normalizer;
		}

		/**
		 * Determine if the cache contains certain independence information.
		 *
		 * @param condition
		 *            A condition in case of conditional independence, null otherwise.
		 * @param a
		 *            The first letter
		 * @param b
		 *            The second letter
		 * @return SAT if the letters are known to be independent (possibly under the given condition), UNSAT if they
		 *         are known to be dependent, and UNKNOWN otherwise.
		 */
		public LBool contains(final S condition, final L a, final L b) {
			final Object key = normalize(condition, a, b);
			final HashRelation<L, L> positive = mPositiveCache.get(key);
			if (positive != null && positive.containsPair(a, b)) {
				return LBool.SAT;
			}

			final HashRelation<L, L> negative = mNegativeCache.get(key);
			if (negative != null && negative.containsPair(a, b)) {
				return LBool.UNSAT;
			}

			return LBool.UNKNOWN;
		}

		/**
		 * Remove all independence and dependence information involving a given letter.
		 *
		 * @param a
		 *            The letter whose information shall be removed.
		 */
		public void remove(final L a) {
			for (final HashRelation<L, L> relation : mPositiveCache.values()) {
				relation.removeDomainElement(a);
				relation.removeRangeElement(a);
			}
			for (final HashRelation<L, L> relation : mNegativeCache.values()) {
				relation.removeDomainElement(a);
				relation.removeRangeElement(a);
			}
		}

		/**
		 * Add information to the cache.
		 *
		 * @param condition
		 *            A condition, or null in case of non-conditional independence.
		 * @param a
		 *            The first letter
		 * @param b
		 *            The second letter
		 * @param independent
		 *            Whether or not the given letters are independent
		 */
		public void cacheResult(final S condition, final L a, final L b, final boolean independent) {
			final Object key = normalize(condition, a, b);
			final Map<Object, HashRelation<L, L>> cache = independent ? mPositiveCache : mNegativeCache;
			final HashRelation<L, L> row = cache.computeIfAbsent(key, x -> new HashRelation<>());
			row.addPair(a, b);
		}

		/**
		 * @return The number of dependent pairs of letters in the cache, across all conditions (if any).
		 */
		public int getNegativeCacheSize() {
			return mNegativeCache.entrySet().stream().collect(Collectors.summingInt(e -> e.getValue().size()));
		}

		/**
		 * @return The number of all independent pairs of letters in the cache, across all conditions (if any).
		 */
		public int getPositiveCacheSize() {
			return mPositiveCache.entrySet().stream().collect(Collectors.summingInt(e -> e.getValue().size()));
		}

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
		public void mergeIndependencies(final L a, final L b, final L ab) {
			for (final HashRelation<L, L> relation : mPositiveCache.values()) {
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

		private Object normalize(final S condition, final L a, final L b) {
			if (condition == null) {
				return null;
			}
			if (mNormalizer == null) {
				return condition;
			}
			return mNormalizer.normalize(condition, a, b);
		}
	}

	/**
	 * An interface used to improve caching for conditional independence relations where some different conditions
	 * induce the same independence between letters.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <S>
	 *            The type of conditions (states) that induce independence.
	 * @param <L>
	 *            The type of letters whose independence is tracked.
	 */
	public interface IConditionNormalizer<S, L> {
		/**
		 * Used to identify conditions which are equivalent with respect to independence of the given letters. This
		 * method must satisfy the following contract:
		 *
		 * For all letters a, b and conditions s1, s2, if normalize(s1, a, b) == normalize(s2, a, b), then a and b are
		 * independent in s1 iff they are independent in s2. Furthermore, null should be returned only if independence
		 * in the given context holds iff independence without context holds.
		 *
		 * In order to have performance benefit, implementations of this method should be significantly more efficient
		 * than the relation for which they are being used.
		 *
		 * @param state
		 *            A condition to be normalized
		 * @param a
		 *            The first letter
		 * @param b
		 *            The second letter
		 * @return An arbitrary value satisfying the contract above.
		 */
		Object normalize(S state, L a, L b);
	}
}
