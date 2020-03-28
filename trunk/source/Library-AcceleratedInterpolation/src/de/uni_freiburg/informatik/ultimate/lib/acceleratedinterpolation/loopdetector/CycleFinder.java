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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.AcceleratedInterpolation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de) This class provides some static oeprations for finding
 *         loops. {@link AcceleratedInterpolation}
 */
public class CycleFinder {

	public CycleFinder() {
	}

	/**
	 * Searches for cycles in a given trace.
	 * 
	 * @param traceOfLocations
	 * @return
	 */
	public Map<IcfgLocation, List<Integer>> getCyclesInTrace(final List<IcfgLocation> traceOfLocations) {
		final Set<IcfgLocation> possLoopHeads = new HashSet<>();
		final Map<IcfgLocation, Integer> locFirstSeen = new HashMap<>();
		final Map<IcfgLocation, List<Integer>> loopHeads = new HashMap<>();

		int i = 0;
		for (final IcfgLocation loc : traceOfLocations) {
			if (loopHeads.containsKey(loc)) {
				final List<Integer> old = loopHeads.get(loc);
				old.add(i);
				loopHeads.replace(loc, old);
			} else if (!possLoopHeads.add(loc)) {
				final ArrayList<Integer> newList = new ArrayList<>();
				final int firstSeen = locFirstSeen.get(loc);
				newList.add(firstSeen);
				newList.add(i);
				loopHeads.put(loc, newList);
			} else {
				locFirstSeen.put(loc, i);
			}
			i++;
		}
		return loopHeads;
	}

	/**
	 * Get a given loop's transitions
	 *
	 * This extracts the smallest repetition of the first loop of loopHead; in particular, this extracts only one loop
	 * per loop head
	 *
	 * @param loopHead
	 *            beginning of the loop
	 * @return
	 *
	 * @return body of the loop
	 */
	public <LETTER extends IIcfgTransition<?>> List<LETTER> getCyclesInTraceNaive(final IcfgLocation loopHead,
			final List<LETTER> trace) {
		int start = 0;
		int end = 0;
		int cnt = 0;
		for (final LETTER loc : trace) {
			if (loc.getSource() == loopHead) {
				if (cnt > start) {
					end = cnt;
				} else {
					start = cnt;
				}
				cnt++;
			}
		}
		return trace.subList(start, end);
	}

	/**
	 * Given a trace of program transitions, this converts them to represent corresponsing program locations.
	 *
	 * @param <LETTER>
	 * @param trace
	 * @return
	 */
	public <LETTER extends IIcfgTransition<?>> List<IcfgLocation> statementsToLocations(final List<LETTER> trace) {
		final List<IcfgLocation> traceLocations = new ArrayList<>();

		for (final LETTER stm : trace) {
			traceLocations.add(stm.getSource());
		}
		traceLocations.add(trace.get(trace.size() - 1).getTarget());
		return traceLocations;
	}
}