/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgToChc plug-in.
 *
 * The ULTIMATE IcfgToChc plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgToChc plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgToChc plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgToChc plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgToChc plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.partialorder;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * A thread-modular preference order is used to select the representatives present in the reduction, i.e., those
 * interleavings that are not pruned. This interface is used for CHC-based sleep set reduction, and is somewhat
 * analogous to {@link de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder.IDfsOrder} in automata-based
 * reduction algorithms.
 *
 * However, thread-modular preference orders are somewhat more restrictive, to allow their usage in parametrized
 * programs, and they are symbolic, to allow usage in the CHC encoding. A thread-modular preference order is given by a
 * transitive binary relation R between CFG locations. If threads i and j are in locations l_i and l_j, respectively,
 * then thread i is preferable to thread j iff (l_i,l_j) in R, and (l_j, l_i) in R implies i < j.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public interface IThreadModularPreferenceOrder {
	/**
	 * Constructs a boolean constraint expressing membership of a pair of CFG locations in the relation underlying this
	 * preference order.
	 *
	 * At least one of {@code loc1} and {@code loc2} is guaranteed to be non-null.
	 *
	 * @param loc1
	 *            The first location of the pair to be considered. May be null.
	 * @param loc1Term
	 *            A term denoting the first location of the pair to be considered.
	 * @param loc2
	 *            The second location of the pair to be considered. May be null.
	 * @param loc2Term
	 *            A term denoting the second location of the pair to be considered.
	 * @param locationMap
	 *            A mapping from locations to the integer value used to represent that location.
	 * @return a constraint over the given terms (including the terms in {@code locationTerms})
	 */
	Term getOrderConstraint(IcfgLocation loc1, Term loc1Term, IcfgLocation loc2, Term loc2Term,
			Map<IcfgLocation, Integer> locationMap);

	boolean isPositional();
}
