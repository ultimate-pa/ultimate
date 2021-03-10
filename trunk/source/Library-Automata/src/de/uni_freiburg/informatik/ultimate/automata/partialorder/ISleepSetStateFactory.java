/*
 * Copyright (C) 2020 Marcel Ebbinghaus
 * Copyright (C) 2020 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Interface for the stateFactory for sleep sets.
 * 
 * @author Marcel Ebbinghaus
 *
 * @param <L> letter
 * @param <S1> state
 * @param <S2> sleep set state
 */
public interface ISleepSetStateFactory<L, S1, S2> extends IEmptyStackStateFactory<S2> {
	/**
	 * Method to create the sleep set state according to a given state and sleep set.
	 * 
	 * @param state
	 * 		The given state
	 * @param sleepset
	 * 		The given sleep set
	 * @return
	 * 		The corresponding sleep set state
	 */
	S2 createSleepSetState(S1 state, Set<L> sleepset);

	/**
	 * Default implementation of the interface, which represents the sleep set state as a pair.
	 * 
	 * @author Marcel Ebbinghaus
	 *
	 * @param <L> letter
	 * @param <S1> state
	 */
	public static class DefaultSleepSetStateFactory<L, S1> implements ISleepSetStateFactory<L, S1, Pair<S1, Set<L>>> {
		@Override
		public Pair<S1, Set<L>> createEmptyStackState() {
			throw new UnsupportedOperationException();
		}

		@Override
		public Pair<S1, Set<L>> createSleepSetState(final S1 state, final Set<L> sleepset) {
			return new Pair<>(state, sleepset);
		}
	}
}
