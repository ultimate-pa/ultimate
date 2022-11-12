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
package de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.abstraction;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IndependenceStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * A simple combination of abstraction and independence: This relation applies abstraction to letters at a fixed
 * abstraction levels and queries an underlying independence relation with the abstracted letters.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <H>
 *            The type of abstraction levels
 * @param <L>
 *            The type of letters
 * @param <S>
 *            The type of states on which independence may be conditional
 */
public class IndependenceRelationWithAbstraction<H, L, S> implements IIndependenceRelation<S, L> {

	private final IIndependenceRelation<S, L> mUnderlying;
	private final IAbstraction<H, L> mAbstraction;
	private final H mLevel;
	private final IndependenceStatisticsDataProvider mStatistics;

	public IndependenceRelationWithAbstraction(final IIndependenceRelation<S, L> underlying,
			final IAbstraction<H, L> abstraction, final H level) {
		mUnderlying = underlying;
		mAbstraction = abstraction;
		mLevel = level;
		mStatistics = new AbstractingStatistics();
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
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
		final L abstractA = mAbstraction.abstractLetter(a, mLevel);
		final L abstractB = mAbstraction.abstractLetter(b, mLevel);
		final Dependence result = mUnderlying.isIndependent(state, abstractA, abstractB);
		mStatistics.reportQuery(result, state != null);
		return result;
	}

	public ILattice<H> getHierarchy() {
		return mAbstraction.getHierarchy();
	}

	public H getLevel() {
		return mLevel;
	}

	private class AbstractingStatistics extends IndependenceStatisticsDataProvider {
		public static final String ABSTRACTION_STATISTICS = "Statistics for Abstraction";

		public AbstractingStatistics() {
			super(IndependenceRelationWithAbstraction.class, mUnderlying);
			forward(ABSTRACTION_STATISTICS, mAbstraction::getStatistics);
		}
	}
}
