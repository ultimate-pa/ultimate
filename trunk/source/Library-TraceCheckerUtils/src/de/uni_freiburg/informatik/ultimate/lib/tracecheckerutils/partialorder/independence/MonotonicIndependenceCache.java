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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedIndependenceRelation.IIndependenceCache;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

/**
 * An {@link IIndependenceCache} implementation that takes advantage of the (assumed) monotonicity of the underlying
 * relation with respect to its conditions.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters whose independence is cached
 */
public class MonotonicIndependenceCache<L> implements IIndependenceCache<IPredicate, L> {
	private final Map<L, Map<L, Set<IPredicate>>> mPositiveCache = new HashMap<>();
	private final Map<L, Map<L, Set<IPredicate>>> mNegativeCache = new HashMap<>();
	private final IPredicateCoverageChecker mCoverageChecker;

	/**
	 * Create a new cache.
	 *
	 * @param coverageChecker
	 *            Used to determine implication between conditions.
	 */
	public MonotonicIndependenceCache(final IPredicateCoverageChecker coverageChecker) {
		mCoverageChecker = coverageChecker;
	}

	@Override
	public LBool contains(final IPredicate condition, final L a, final L b) {
		// Check if a and b are known to be independent under some weaker context p.
		final Set<IPredicate> positiveEntry = getCacheEntry(mPositiveCache, a, b);
		final boolean positive =
				positiveEntry.stream().anyMatch(p -> mCoverageChecker.isCovered(condition, p) == Validity.VALID);
		if (positive) {
			return LBool.SAT;
		}

		// Check if a and b are known to be dependent under some stronger context p.
		final Set<IPredicate> negativeEntry = getCacheEntry(mNegativeCache, a, b);
		final boolean negative =
				negativeEntry.stream().anyMatch(p -> mCoverageChecker.isCovered(p, condition) == Validity.VALID);
		if (negative) {
			return LBool.UNSAT;
		}

		return LBool.UNKNOWN;
	}

	private Set<IPredicate> getCacheEntry(final Map<L, Map<L, Set<IPredicate>>> cache, final L a, final L b) {
		final Map<L, Set<IPredicate>> row = cache.get(a);
		if (row == null) {
			return Collections.emptySet();
		}
		final Set<IPredicate> entry = row.get(b);
		if (entry == null) {
			return Collections.emptySet();
		}
		return entry;
	}

	@Override
	public void remove(final L a) {
		mPositiveCache.remove(a);
		mNegativeCache.remove(a);
		for (final Map<L, Set<IPredicate>> row : mPositiveCache.values()) {
			row.remove(a);
		}
		for (final Map<L, Set<IPredicate>> row : mNegativeCache.values()) {
			row.remove(a);
		}
	}

	@Override
	public void cacheResult(final IPredicate condition, final L a, final L b, final boolean independent) {
		if (independent) {
			addPositiveCacheEntry(condition, a, b);
		} else {
			addNegativeCacheEntry(condition, a, b);
		}
	}

	private void addPositiveCacheEntry(final IPredicate state, final L a, final L b) {
		final Map<L, Set<IPredicate>> row = mPositiveCache.computeIfAbsent(a, x -> new HashMap<>());
		final Set<IPredicate> entry = row.computeIfAbsent(b, x -> new HashSet<>());
		entry.removeIf(p -> mCoverageChecker.isCovered(p, state) == Validity.VALID);
		entry.add(state);
	}

	private void addNegativeCacheEntry(final IPredicate state, final L a, final L b) {
		final Map<L, Set<IPredicate>> row = mNegativeCache.computeIfAbsent(a, x -> new HashMap<>());
		final Set<IPredicate> entry = row.computeIfAbsent(b, x -> new HashSet<>());
		entry.removeIf(p -> mCoverageChecker.isCovered(state, p) == Validity.VALID);
		entry.add(state);
	}

	/**
	 * Currently not supported by this implementation.
	 */
	@Override
	public void mergeIndependencies(final L a, final L b, final L ab) {
		// Implementing this might require infimum and supremum operations on IPredicate.
		throw new UnsupportedOperationException("This cache does not yet implement independence merging");
	}
}