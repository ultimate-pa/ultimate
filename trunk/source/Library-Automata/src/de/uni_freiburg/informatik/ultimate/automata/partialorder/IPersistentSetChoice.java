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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.Comparator;
import java.util.Set;

/**
 * An interface for the computation of persistent sets, used in persistent set reduction.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters
 * @param <S>
 *            The type of states
 */
public interface IPersistentSetChoice<L, S> {
	/**
	 * Given a state, returns a set of letters forming a persistent set for this state.
	 *
	 * @param state
	 *            A state of the reduction's input automaton
	 * @return the persistent set
	 */
	Set<L> persistentSet(final S state);

	/**
	 * A sleep set order that can be used with persistent set reduction.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 * @param <S>
	 */
	public class PersistentSleepOrder<L, S> implements ISleepSetOrder<S, L> {
		private final IPersistentSetChoice<L, S> mPersistent;
		private final ISleepSetOrder<S, L> mUnderlying;

		public PersistentSleepOrder(final IPersistentSetChoice<L, S> persistent,
				final ISleepSetOrder<S, L> underlying) {
			mPersistent = persistent;
			mUnderlying = underlying;
		}

		@Override
		public Comparator<L> getOrder(final S state) {
			final Set<L> persistent = mPersistent.persistentSet(state);
			final Comparator<L> comparator = mUnderlying.getOrder(state);
			return (a, b) -> {
				if (persistent.contains(a) && !persistent.contains(b)) {
					return -1;
				} else if (persistent.contains(b) && !persistent.contains(a)) {
					return 1;
				}
				return comparator.compare(a, b);
			};
		}
	}
}
