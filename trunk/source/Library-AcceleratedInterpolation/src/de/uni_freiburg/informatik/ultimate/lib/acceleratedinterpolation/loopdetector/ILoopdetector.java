/*
 * Copyright (C) 2020 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE accelerated interpolation library .
 *
 * The ULTIMATE framework is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE framework is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE accelerated interpolation library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PDR library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE accelerated interpolation library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.loopdetector;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Interface for a loop detector needed for accelerated interpolation.
 *
 * @author Jonas Werner <wernerj@informatik.uni-freiburg.de>
 *
 * @param <LOC>
 *            Location Types,
 * @param <LETTER>
 *            Transition types
 */
public interface ILoopdetector<LOC, LETTER> {

	/**
	 * Return loops as a map from location to possible loop paths.
	 *
	 * @return
	 */
	Map<LOC, Set<List<LETTER>>> getLoops();

	Map<LOC, Set<List<UnmodifiableTransFormula>>> getLoopsTf();

	Map<LOC, Set<List<UnmodifiableTransFormula>>> getNestedLoopsTf();

	/**
	 * Return final transitions of a loop, e.g. transitions that return to the main program. Again as a location
	 * transition pair.
	 *
	 * @return
	 */
	Map<LOC, LETTER> getLoopExitTransitions();

	/**
	 * Return the size of a loop as an integer pari. The first integer is the first occurence of the loop head, the last
	 * is the last. Subsequent loophead findings between those two are subsumed by the size.
	 *
	 * @return
	 */
	Map<LOC, Pair<Integer, Integer>> getLoopSize();

	/**
	 * Maps a nesting loop head to a nested loophead
	 *
	 * @return
	 */
	Map<LOC, LOC> getNestingRelation();

	/**
	 * Map of Loops that are nested
	 *
	 * @return
	 */
	Map<LOC, Set<List<LETTER>>> getNestedLoops();

}
