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

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IndependenceStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;

/**
 * A wrapper independence relation that forwards queries to an underlying relation, unless the two actions are from the
 * same thread. If they are, then this relation considers them to be dependent.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <S>
 *            The type of conditions (relevant only for the underlying relation)
 * @param <L>
 *            The type of letters whose independence is tracked.
 */
public class ThreadSeparatingIndependenceRelation<S, L extends IAction> implements IIndependenceRelation<S, L> {

	private final IIndependenceRelation<S, L> mUnderlying;
	private final SeparatingStatistics mStatistics;

	public ThreadSeparatingIndependenceRelation(final IIndependenceRelation<S, L> underlying) {
		mUnderlying = underlying;
		mStatistics = new SeparatingStatistics();
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
		if (fromSameThread(a, b)) {
			mStatistics.reportSameThreadQuery(state != null);
			return Dependence.DEPENDENT;
		}
		final Dependence result = mUnderlying.isIndependent(state, a, b);
		mStatistics.reportQuery(result, state != null);
		return result;
	}

	private boolean fromSameThread(final L a, final L b) {
		return Objects.equals(a.getPrecedingProcedure(), b.getPrecedingProcedure());
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	private class SeparatingStatistics extends IndependenceStatisticsDataProvider {
		public static final String SAME_THREAD_QUERIES = "Independence queries for same thread";

		private int mSameThreadQueries;

		public SeparatingStatistics() {
			super(ThreadSeparatingIndependenceRelation.class, mUnderlying);
			declare(SAME_THREAD_QUERIES, () -> mSameThreadQueries, KeyType.COUNTER);
		}

		private void reportSameThreadQuery(final boolean conditional) {
			mSameThreadQueries++;
			reportDependentQuery(conditional);
		}
	}
}
