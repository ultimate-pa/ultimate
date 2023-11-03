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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.ISleepMapStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * Computes persistent sets wrt. a sequence of independence relations.
 *
 * This is only sound in combination with a DFS order compatible with all underlying persistent set choices!
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 * @param <S>
 */
public class MultiPersistentSetChoice<L, S> implements IPersistentSetChoice<L, S> {

	private final List<IPersistentSetChoice<L, S>> mUnderlying;
	private final ISleepMapStateFactory<L, ?, S> mSleepMapFactory;

	public MultiPersistentSetChoice(final List<IPersistentSetChoice<L, S>> underlying,
			final ISleepMapStateFactory<L, ?, S> sleepMapFactory) {
		mUnderlying = underlying;
		mSleepMapFactory = sleepMapFactory;
	}

	@Override
	public Set<L> persistentSet(final S state) {
		Set<L> result = null;

		final var it = mUnderlying.iterator();
		final int budget = mSleepMapFactory.getBudget(state);
		for (int i = 0; i < budget; ++i) {
			assert it.hasNext() : "Budget exceeds number of persistent set computations";
			final var persistent = it.next().persistentSet(state);

			if (persistent == null) {
				continue;
			}
			result = result == null ? persistent : DataStructureUtils.intersection(result, persistent);
		}

		return result;
	}

	@Override
	public boolean ensuresCompatibility(final IDfsOrder<L, S> order) {
		assert mUnderlying.stream().allMatch(p -> p.ensuresCompatibility(order));
		return true;
	}
}
