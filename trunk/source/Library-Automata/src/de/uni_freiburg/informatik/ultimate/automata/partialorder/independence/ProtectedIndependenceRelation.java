/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;

/**
 * An independence relation that protects an underlying relation from certain queries (e.g. queries that are expected to
 * be expensive) and returns {@code Dependence.UNKNOWN} instead.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <S>
 *            The type of states (i.e. conditions) of the relation
 * @param <L>
 *            The type of letters that are checked for independence
 */
public class ProtectedIndependenceRelation<S, L> implements IIndependenceRelation<S, L> {
	private final IIndependenceRelation<S, L> mUnderlying;
	private final IFilter<L> mFilter;
	private final Statistics mStatistics;

	/**
	 * Create a new protecting wrapper around a given relation.
	 *
	 * @param underlying
	 *            The underlying relation to protect
	 * @param filter
	 *            A filter that determines which queries are allowed and which simply return {@code UNKNOWN}
	 */
	public ProtectedIndependenceRelation(final IIndependenceRelation<S, L> underlying, final IFilter<L> filter) {
		mUnderlying = underlying;
		mFilter = filter;
		mStatistics = new Statistics();
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
		if (mFilter.test(a) && mFilter.test(b)) {
			final var result = mUnderlying.isIndependent(state, a, b);
			mFilter.update(a, b, result);
			mStatistics.reportQuery(result, state != null);
			return result;
		}
		mStatistics.reportProtectedQuery(state != null);
		return Dependence.UNKNOWN;
	}

	@Override
	public ISymbolicIndependenceRelation<L, S> getSymbolicRelation() {
		final var underlying = mUnderlying.getSymbolicRelation();
		if (underlying == null) {
			return null;
		}
		return new SymbolicProtectedIndependence(underlying);
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	/**
	 * A filter predicate for independence relations. The filter can also learn from past queries and therefore change
	 * over time.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 *            The type of letters being filtered
	 */
	@FunctionalInterface
	public interface IFilter<L> {
		/**
		 * Determines if a given letter passes the filter.
		 *
		 * @param a
		 *            The letter to test
		 * @return true if the letter passes the filter, i.e., a query involving this letter can be performed; false if
		 *         queries involving this letter should not be performed.
		 */
		boolean test(L a);

		/**
		 * Called whenever a query was performed, to allow the filter to update its internal state.
		 *
		 * @param a
		 *            The first letter
		 * @param b
		 *            The second letter
		 * @param result
		 *            The result of the independence query
		 */
		default void update(final L a, final L b, final Dependence result) {
			// by default, do nothing
		}
	}

	private class SymbolicProtectedIndependence implements ISymbolicIndependenceRelation<L, S> {
		private final ISymbolicIndependenceRelation<L, S> mUnderlyingSymbolic;

		public SymbolicProtectedIndependence(final ISymbolicIndependenceRelation<L, S> underlyingSymbolic) {
			mUnderlyingSymbolic = underlyingSymbolic;
		}

		@Override
		public S getCommutativityCondition(final S condition, final L a, final L b) {
			if (mFilter.test(a) && mFilter.test(b)) {
				return mUnderlyingSymbolic.getCommutativityCondition(condition, a, b);
			}
			return null;
		}

		@Override
		public boolean isSymmetric() {
			return mUnderlyingSymbolic.isSymmetric();
		}

		@Override
		public boolean isConditional() {
			return mUnderlyingSymbolic.isConditional();
		}
	}

	private final class Statistics extends IndependenceStatisticsDataProvider {
		public static final String PROTECTED_QUERIES = "Protected Queries";

		private int mProtectedQueries;

		private Statistics() {
			super(ProtectedIndependenceRelation.class, mUnderlying);
			declare(PROTECTED_QUERIES, () -> mProtectedQueries, KeyType.COUNTER);
		}

		private void reportProtectedQuery(final boolean isConditional) {
			mProtectedQueries++;
			reportQuery(Dependence.UNKNOWN, isConditional);
		}
	}
}
