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

import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * A family of abstraction functions that take a letter as input and return an "abstracted" letter. Here we do not
 * prescribe a fixed notion of "abstraction", but a client domain (e.g. program analysis) may fix such a notion.
 *
 * The family of abstraction functions is indexed by so-called "abstraction levels", which form a lattice structure.
 * Abstraction with the lattice's bottom element corresponds to the identity, and abstraction with the top element is so
 * broad that all abstracted letters commute.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <H>
 *            The type of abstraction levels
 * @param <L>
 *            The type of letters to abstract
 */
public interface IAbstraction<H, L> {
	/**
	 * The lattice of abstraction levels
	 */
	ILattice<H> getHierarchy();

	/**
	 * Applies abstraction to a letter.
	 *
	 * @param input
	 *            The letter to abstract
	 * @param level
	 *            The abstraction level
	 * @return the abstracted letter
	 */
	L abstractLetter(L input, H level);

	/**
	 * Computes a lower abstraction level down to which the abstraction will return the same result for a given letter
	 * as for the given level. This information can be used to avoid redundant computations.
	 *
	 * The default implementation simply returns the given level.
	 *
	 * @param input
	 *            A letter to abstract
	 * @param level
	 *            An initial abstraction level
	 * @return an abstraction level x such that x &lt;= level and for all y such that x &lt;= y &lt;= level, a call
	 *         <code>abstractLetter(input, y)</code> will return the same (or an equivalent) result as the call
	 *         <code>abstractLetter(input, level)</code>.
	 */
	default H restrict(final L input, final H level) {
		return level;
	}

	/**
	 * An optional method that allows collecting statistics about the history of queries made to this independence
	 * relation. The default implementation does not provide any statistics.
	 *
	 * @return a statistics provider with implementation-defined data
	 */
	default IStatisticsDataProvider getStatistics() {
		return new AbstractStatisticsDataProvider() {
			// By default, no statistics are collected.
		};
	}
}
