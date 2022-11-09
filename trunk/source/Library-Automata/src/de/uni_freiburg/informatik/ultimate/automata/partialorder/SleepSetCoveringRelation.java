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

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.CoveringOptimizationVisitor.ICoveringRelation;

/**
 * A covering relation for {@link MinimalSleepSetReduction}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters
 * @param <S>
 *            The type of states in the underlying automaton
 * @param <R>
 *            The type of states in the reduction automaton
 */
public class SleepSetCoveringRelation<L, S, R> implements ICoveringRelation<R> {
	private final ISleepSetStateFactory<L, S, R> mStateFactory;
	private final ICoveringRelation<S> mUnderlying;

	/**
	 * Create a new instance of the covering relation, using the identity as covering relation of the reduction's
	 * underlying automaton.
	 *
	 * @param stateFactory
	 *            The state factory used by the reduction
	 */
	public SleepSetCoveringRelation(final ISleepSetStateFactory<L, S, R> stateFactory) {
		this(stateFactory, Objects::equals);
	}

	/**
	 * Create a new instance of the covering relation.
	 *
	 * @param stateFactory
	 *            The state factory used by the reduction
	 * @param underlying
	 *            A covering relation on the reduction's underlying automaton
	 */
	public SleepSetCoveringRelation(final ISleepSetStateFactory<L, S, R> stateFactory,
			final ICoveringRelation<S> underlying) {
		mStateFactory = stateFactory;
		mUnderlying = underlying;
	}

	@Override
	public boolean covers(final R oldState, final R newState) {
		return mUnderlying.covers(mStateFactory.getOriginalState(oldState), mStateFactory.getOriginalState(newState))
				&& mStateFactory.getSleepSet(newState).containsAll(mStateFactory.getSleepSet(oldState));
	}

	@Override
	public Object getKey(final R state) {
		return mUnderlying.getKey(mStateFactory.getOriginalState(state));
	}
}
