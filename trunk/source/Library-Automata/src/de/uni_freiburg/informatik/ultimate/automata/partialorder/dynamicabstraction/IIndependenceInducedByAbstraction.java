/*
 * Copyright (C) 2023 Veronika Klasen
 * Copyright (C) 2023 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.automata.partialorder.dynamicabstraction;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;

/**
 * Provides independence relations induced by a given abstraction level.
 *
 * @param <S>
 *            The type of automaton states
 * @param <H>
 *            The type of abstraction levels
 */
public interface IIndependenceInducedByAbstraction<S, L, H> {
	/**
	 * Return the independence relation induced by the given abstraction level
	 *
	 * @param abstractionLevel
	 *            The abstraction level. For instance, if the abstraction is performed through projection of variables,
	 *            this should be the set of program variables that are not abstracted away.
	 * @return The independence relation induced by the given abstraction level
	 */
	IIndependenceRelation<S, L> getInducedIndependence(H abstractionLevel);

	ILattice<H> getAbstractionLattice();
}
