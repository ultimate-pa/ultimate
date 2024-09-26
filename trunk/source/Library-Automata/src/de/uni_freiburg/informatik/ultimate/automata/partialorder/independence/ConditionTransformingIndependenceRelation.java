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

import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * A wrapper independence relation that applies a transformation on the condition before proxying the call to an
 * underlying relation.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <S>
 *            The type of condition before the transformation
 * @param <T>
 *            The type of condition after the transformation
 * @param <L>
 *            The type of letters
 */
public class ConditionTransformingIndependenceRelation<S, T, L> implements IIndependenceRelation<S, L> {
	private final IIndependenceRelation<T, L> mUnderlying;
	private final Function<S, T> mTransformer;
	private final Function<T, S> mBackTransformer;
	private final boolean mConditional;
	private final IndependenceStatisticsDataProvider mStatistics;

	/**
	 * Creates a new instance.
	 *
	 * @param underlying
	 *            The underlying conditional independence relation.
	 * @param transformer
	 *            A transformation applied to conditions.
	 */
	public ConditionTransformingIndependenceRelation(final IIndependenceRelation<T, L> underlying,
			final Function<S, T> transformer) {
		// TODO allow passing backtransformer
		this(underlying, transformer, null, underlying.isConditional());
	}

	private ConditionTransformingIndependenceRelation(final IIndependenceRelation<T, L> underlying,
			final Function<S, T> transformer, final Function<T, S> backtransformer, final boolean conditional) {
		mUnderlying = underlying;
		mTransformer = transformer;
		mBackTransformer = backtransformer;
		mConditional = conditional;
		mStatistics =
				new IndependenceStatisticsDataProvider(ConditionTransformingIndependenceRelation.class, underlying);
	}

	@Override
	public boolean isSymmetric() {
		return mUnderlying.isSymmetric();
	}

	@Override
	public boolean isConditional() {
		return mConditional;
	}

	@Override
	public Dependence isIndependent(final S state, final L a, final L b) {
		final T condition = state == null ? null : mTransformer.apply(state);
		final Dependence result = mUnderlying.isIndependent(condition, a, b);
		mStatistics.reportQuery(result, condition != null);
		return result;
	}

	@Override
	public ISymbolicIndependenceRelation<L, S> getSymbolicRelation() {
		if (!mConditional || mBackTransformer == null) {
			return null;
		}
		final var underlying = mUnderlying.getSymbolicRelation();
		if (underlying == null) {
			return null;
		}
		return new SymbolicConditionTransformingIndependence(underlying);
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	/**
	 * Provides a wrapper for unconditional independence relations. This can be used when an conditional independence
	 * relation (with conditions of a certain type) is expected. It can alternatively be used to forcibly make a
	 * conditional independence relation behave as unconditional.
	 *
	 * @param <S>
	 *            The expected type of conditions (conditions will however be ignored)
	 * @param <L>
	 *            The type of letters
	 * @param underlying
	 *            The underlying relations. This is treated as unconditional, even if it is not.
	 * @return A new independence relation that discards conditions and then calls the underlying relation.
	 */
	public static <S, L> IIndependenceRelation<S, L> unconditional(final IIndependenceRelation<?, L> underlying) {
		return new ConditionTransformingIndependenceRelation<>(underlying, x -> null, null, false);
	}

	private class SymbolicConditionTransformingIndependence implements ISymbolicIndependenceRelation<L, S> {
		private final ISymbolicIndependenceRelation<L, T> mUnderlyingSymbolic;

		public SymbolicConditionTransformingIndependence(final ISymbolicIndependenceRelation<L, T> underlyingSymbolic) {
			mUnderlyingSymbolic = underlyingSymbolic;
		}

		@Override
		public S getCommutativityCondition(final L a, final L b) {
			final T condition = mUnderlyingSymbolic.getCommutativityCondition(a, b);
			if (condition == null) {
				return null;
			}
			return mBackTransformer.apply(condition);
		}

		@Override
		public boolean isSymmetric() {
			return mUnderlyingSymbolic.isSymmetric();
		}
	}
}
