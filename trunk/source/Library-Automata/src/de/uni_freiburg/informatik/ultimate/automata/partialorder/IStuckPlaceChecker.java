/*
 * Copyright (C) 2021 Dennis Wölfing
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

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;

/**
 * An interface that supports checking whether execution might get stuck in a place.
 *
 * @param <L>
 *            The type of the letters in the Petri net.
 * @param <P>
 *            The type of the places in the Petri net.
 */
public interface IStuckPlaceChecker<L, P> {
	/**
	 * Checks whether execution might get stuck at the given place. This is the case if there exists a valuation for
	 * which none of the successor transitions' formulas is satisfied. This function will return true if this property
	 * cannot be proven. Note that predecessor locations of the transitions are not taken into account. They are assumed
	 * to be not more restrictive than the formulas. This function may cache the result.
	 *
	 * @param petriNet
	 *            The Petri net.
	 * @param place
	 *            A place in the Petri net.
	 * @return false if there is always successor transition with a satisfied formula, true if there might not be one.
	 */
	boolean mightGetStuck(IPetriNet<L, P> petriNet, P place);
}
