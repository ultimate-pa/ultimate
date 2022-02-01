/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation;

import java.util.List;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IndependenceStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.Aggregate;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.PrettyPrint;

/**
 * An independence relation that allows splitting a condition into multiple parts and proxying requests for each part to
 * an underlying relation.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <S>
 *            The type of conditions to be split
 * @param <L>
 *            The type of letters whose independence is tracked
 */
public class DistributingIndependenceRelation<S, L> implements IIndependenceRelation<S, L> {
	private final List<IIndependenceRelation<S, L>> mRelations;
	private final Function<S, S[]> mDistribution;
	private final boolean mSymmetric;
	private final boolean mConditional;
	private final DistributingStatistics mStatistics;

	public DistributingIndependenceRelation(final List<IIndependenceRelation<S, L>> relations,
			final Function<S, S[]> distribution) {
		mRelations = relations;
		mDistribution = distribution;
		mSymmetric = relations.stream().allMatch(IIndependenceRelation::isSymmetric);
		mConditional = relations.stream().anyMatch(IIndependenceRelation::isConditional);
		mStatistics = new DistributingStatistics();
	}

	@Override
	public boolean isSymmetric() {
		return mSymmetric;
	}

	@Override
	public boolean isConditional() {
		return mConditional;
	}

	@Override
	public boolean contains(final S state, final L a, final L b) {
		final S[] conjuncts = mDistribution.apply(state);
		assert conjuncts.length == mRelations.size();
		for (int i = 0; i < mRelations.size(); ++i) {
			mStatistics.reportQueriedIndex(i);
			if (mRelations.get(i).contains(conjuncts[i], a, b)) {
				mStatistics.reportPositiveQuery(state != null);
				return true;
			}
		}
		mStatistics.reportNegativeQuery(state != null);
		return false;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	private class DistributingStatistics extends IndependenceStatisticsDataProvider {
		public static final String MAX_QUERIED_INDEX = "Maximal queried relation";

		private int mMaxQueriedIndex = -1;

		public DistributingStatistics() {
			super(DistributingIndependenceRelation.class, mRelations);
			declare(MAX_QUERIED_INDEX, () -> mMaxQueriedIndex, Aggregate::intMax, PrettyPrint::keyColonData);
		}

		private void reportQueriedIndex(final int index) {
			if (mMaxQueriedIndex < index) {
				mMaxQueriedIndex = index;
			}
		}
	}
}