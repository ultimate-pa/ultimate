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

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * An independence relation that represents the union of several independence relations. This can in particular be used
 * to combine an efficient but incomplete check with a more computation-intensive complete check.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 *            The type of conditions (or "states") the relation depends on (if any of the underlying relations does)
 * @param <L>
 *            The type of letters whose independence is being tracked
 */
public class UnionIndependenceRelation<STATE, L> implements IIndependenceRelation<STATE, L> {

	private final Collection<IIndependenceRelation<STATE, L>> mRelations;
	private final boolean mSymmetric;
	private final boolean mConditional;
	private final IndependenceStatisticsDataProvider mStatistics;

	public UnionIndependenceRelation(final Collection<IIndependenceRelation<STATE, L>> relations) {
		mRelations = relations;
		mSymmetric = relations.stream().allMatch(IIndependenceRelation::isSymmetric);
		mConditional = relations.stream().anyMatch(IIndependenceRelation::isConditional);
		mStatistics = new IndependenceStatisticsDataProvider(UnionIndependenceRelation.class, mRelations);
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
	public Dependence isIndependent(final STATE state, final L a, final L b) {
		boolean anyUnknown = false;

		for (final var relation : mRelations) {
			final var result = relation.isIndependent(state, a, b);
			if (result == Dependence.INDEPENDENT) {
				mStatistics.reportIndependentQuery(state != null);
				return Dependence.INDEPENDENT;
			}
			anyUnknown |= result == Dependence.UNKNOWN;
		}

		if (anyUnknown) {
			mStatistics.reportUnknownQuery(state != null);
			return Dependence.UNKNOWN;
		}

		mStatistics.reportDependentQuery(state != null);
		return Dependence.DEPENDENT;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}
}
