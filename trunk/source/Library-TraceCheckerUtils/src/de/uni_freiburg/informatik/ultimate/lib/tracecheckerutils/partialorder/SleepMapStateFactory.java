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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.ISleepMapStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.SleepMap;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

class SleepMapStateFactory<L> implements ISleepMapStateFactory<L, IPredicate, IPredicate> {

	private final IPredicate mEmptyStack;

	private final NestedMap3<IPredicate, SleepMap<L, IPredicate>, Integer, SleepMapPredicate<L>> mMap =
			new NestedMap3<>();

	public SleepMapStateFactory(final PredicateFactory predicateFactory) {
		mEmptyStack = predicateFactory.newEmptyStackPredicate();
	}

	@Override
	public IPredicate createEmptyStackState() {
		return mEmptyStack;
	}

	@Override
	public IPredicate createSleepMapState(final IPredicate state, final SleepMap<L, IPredicate> sleepMap,
			final int budget) {
		final SleepMapPredicate<L> existing = mMap.get(state, sleepMap, budget);
		if (existing != null) {
			return existing;
		}

		final SleepMapPredicate<L> predicate = new SleepMapPredicate<>((IMLPredicate) state, sleepMap, budget);
		mMap.put(state, sleepMap, budget, predicate);
		return predicate;
	}

	@Override
	public IPredicate getOriginalState(final IPredicate sleepMapState) {
		return ((SleepMapPredicate<?>) sleepMapState).getUnderlying();
	}

	@Override
	public SleepMap<L, IPredicate> getSleepMap(final IPredicate sleepMapState) {
		return ((SleepMapPredicate<L>) sleepMapState).getSleepMap();
	}

	@Override
	public int getBudget(final IPredicate sleepMapState) {
		return ((SleepMapPredicate<?>) sleepMapState).getBudget();
	}
}
