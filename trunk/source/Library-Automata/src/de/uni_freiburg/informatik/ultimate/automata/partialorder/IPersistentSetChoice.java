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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * An interface for the computation of persistent sets, used in persistent set reduction.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters in the persistent sets
 * @param <S>
 *            The type of states for which persistent sets are computed
 */
public interface IPersistentSetChoice<L, S> {
	/**
	 * Given a state, returns a set of letters, such that some subset is a persistent set for this state. Return null to
	 * represent the trivial persistent set.
	 *
	 * @param state
	 *            A state of the reduction's input automaton
	 * @return the (superset of a) persistent set, or null
	 */
	Set<L> persistentSet(final S state);

	/**
	 * An optional method that allows collecting statistics about the history of persistent set computations. The
	 * default implementation does not provide any statistics.
	 *
	 * @return a statistics provider with implementation-defined data
	 */
	default IStatisticsDataProvider getStatistics() {
		return new AbstractStatisticsDataProvider() {
			// By default, no statistics are collected.
		};
	}

	default boolean ensuresCompatibility(final IDfsOrder<L, S> order) {
		return false;
	}
}
