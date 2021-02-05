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
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedIndependenceRelation.IIndependenceCache;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

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

	private final Map<Object, HashRelation<L, L>> mPositiveCache = new HashMap<>();
	private final Map<Object, HashRelation<L, L>> mNegativeCache = new HashMap<>();
	private final DefaultIndependenceCache.IConditionNormalizer<S, L> mNormalizer;

	/**
	 * Create a cache.
	 *
	 * @param normalizer
	 *            Can be used to improve caching efficiency. See {@link DefaultIndependenceCache.IConditionNormalizer}
	 *            for details.
	 */
	public DefaultIndependenceCache(final DefaultIndependenceCache.IConditionNormalizer<S, L> normalizer) {
		mNormalizer = normalizer;
	}

	@Override
	public LBool contains(final S condition, final L a, final L b) {
		final HashRelation<L, L> globalPositive = mPositiveCache.get(null);
		if (globalPositive != null && globalPositive.containsPair(a, b)) {
			return LBool.SAT;
		}

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

	@Override
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

	@Override
	public void cacheResult(final S condition, final L a, final L b, final boolean independent) {
		final Object key = normalize(condition, a, b);
		final Map<Object, HashRelation<L, L>> cache = independent ? mPositiveCache : mNegativeCache;
		final HashRelation<L, L> row = cache.computeIfAbsent(key, x -> new HashRelation<>());
		row.addPair(a, b);
	}

	@Override
	public int getNegativeCacheSize() {
		return mNegativeCache.entrySet().stream().collect(Collectors.summingInt(e -> e.getValue().size()));
	}

	@Override
	public int getPositiveCacheSize() {
		return mPositiveCache.entrySet().stream().collect(Collectors.summingInt(e -> e.getValue().size()));
	}

	@Override
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