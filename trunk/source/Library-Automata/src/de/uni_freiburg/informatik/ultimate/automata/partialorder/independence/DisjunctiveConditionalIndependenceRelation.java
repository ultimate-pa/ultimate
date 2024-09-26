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

import java.util.Collection;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.statistics.Aggregate;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.PrettyPrint;

/**
 * An independence relation which checks if any condition in a given collection of conditions leads to independence of
 * the given letters. For an empty collection of conditions, checks for unconditional independence of the given letters.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters
 * @param <S>
 *            The type of conditions
 * @param <C>
 *            The type of collection
 */
public class DisjunctiveConditionalIndependenceRelation<L, S, C extends Collection<S>>
		implements IIndependenceRelation<C, L> {
	private final IIndependenceRelation<S, L> mUnderlying;
	private final Function<S, C> mBuildSingleton;
	private final DisjunctiveStatistics mStatistics;

	/**
	 * Creates a new instance.
	 *
	 * @param underlying
	 *            The underlying relation which is queried for individual conditions. This relation must be conditional.
	 */
	public DisjunctiveConditionalIndependenceRelation(final IIndependenceRelation<S, L> underlying) {
		this(underlying, null);
	}

	/**
	 * Creates a new instance which also provides a corresponding {@link ISymbolicIndependenceRelation}.
	 *
	 * @param underlying
	 *            The underlying relation which is queried for individual conditions. This relation must be conditional.
	 * @param buildSingleton
	 *            A function that builds a singleton collection of type {@code C} from an element of type {@code S}.
	 *            This is used for the corresponding {@link ISymbolicIndependenceRelation}. If this parameter is
	 *            {@code null}, no symbolic relation can be created.
	 */
	public DisjunctiveConditionalIndependenceRelation(final IIndependenceRelation<S, L> underlying,
			final Function<S, C> buildSingleton) {
		assert underlying.isConditional() : "Only makes sense for conditional independence relations";
		mUnderlying = underlying;
		mBuildSingleton = buildSingleton;
		mStatistics = new DisjunctiveStatistics();
	}

	@Override
	public boolean isSymmetric() {
		return mUnderlying.isSymmetric();
	}

	@Override
	public boolean isConditional() {
		return true;
	}

	@Override
	public Dependence isIndependent(final C state, final L a, final L b) {
		if (state == null || state.isEmpty()) {
			final Dependence result = mUnderlying.isIndependent(null, a, b);
			mStatistics.reportQuery(result, false);
			return result;
		}

		boolean anyUnknown = false;
		int i = 0;
		for (final S condition : state) {
			mStatistics.reportQueriedIndex(i);
			final Dependence result = mUnderlying.isIndependent(condition, a, b);
			if (result == Dependence.INDEPENDENT) {
				mStatistics.reportIndependentQuery(true);
				return Dependence.INDEPENDENT;
			}
			anyUnknown |= result == Dependence.UNKNOWN;
			i++;
		}

		if (anyUnknown) {
			mStatistics.reportUnknownQuery(true);
			return Dependence.UNKNOWN;
		}

		mStatistics.reportDependentQuery(true);
		return Dependence.DEPENDENT;
	}

	@Override
	public ISymbolicIndependenceRelation<L, C> getSymbolicRelation() {
		if (mBuildSingleton == null) {
			return null;
		}
		final var underlying = mUnderlying.getSymbolicRelation();
		if (underlying == null) {
			return null;
		}
		return new SymbolicDisjunctiveIndependence(underlying);
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	private class SymbolicDisjunctiveIndependence implements ISymbolicIndependenceRelation<L, C> {
		private final ISymbolicIndependenceRelation<L, S> mUnderlyingSymbolic;

		public SymbolicDisjunctiveIndependence(final ISymbolicIndependenceRelation<L, S> underlyingSymbolic) {
			mUnderlyingSymbolic = underlyingSymbolic;
		}

		@Override
		public C getCommutativityCondition(final L a, final L b) {
			final S condition = mUnderlyingSymbolic.getCommutativityCondition(a, b);
			if (condition == null) {
				return null;
			}
			return mBuildSingleton.apply(condition);
		}

		@Override
		public boolean isSymmetric() {
			return mUnderlyingSymbolic.isSymmetric();
		}
	}

	private class DisjunctiveStatistics extends IndependenceStatisticsDataProvider {
		public static final String MAX_QUERIED_INDEX = "Maximal queried relation";

		private int mMaxQueriedIndex = -1;

		public DisjunctiveStatistics() {
			super(DisjunctiveConditionalIndependenceRelation.class, mUnderlying);
			declare(MAX_QUERIED_INDEX, () -> mMaxQueriedIndex, Aggregate::intMax, PrettyPrint::keyColonData);
		}

		private void reportQueriedIndex(final int index) {
			if (mMaxQueriedIndex < index) {
				mMaxQueriedIndex = index;
			}
		}
	}
}
