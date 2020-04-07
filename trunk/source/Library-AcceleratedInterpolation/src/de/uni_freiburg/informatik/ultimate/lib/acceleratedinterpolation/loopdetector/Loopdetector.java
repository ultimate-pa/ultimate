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
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.AcceleratedInterpolation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de) This class represents the loop detector needed for
 *         {@link AcceleratedInterpolation}
 */
public class Loopdetector<LETTER extends IIcfgTransition<?>> {

	private List<LETTER> mTrace;
	private final List<IcfgLocation> mTraceLocations;
	private final ILogger mLogger;

	private final CycleFinder mCycleFinder;

	public Loopdetector(final List<LETTER> trace, final ILogger logger) {
		mLogger = logger;
		mTrace = trace;
		mCycleFinder = new CycleFinder();
		mTraceLocations = mCycleFinder.statementsToLocations(mTrace);

		mLogger.debug("Loopdetector created.");
	}

	/**
	 * Calculates loops from a given trace.
	 */
	public Map<IcfgLocation, Set<List<LETTER>>> getLoops() {
		final Map<IcfgLocation, List<Integer>> possibleCycles = mCycleFinder.getCyclesInTrace(mTraceLocations);
		mLogger.debug("Found Loopheads");
		final Set<IcfgLocation> nestedCycles = getNestedCycles(possibleCycles);
		final Map<IcfgLocation, Set<List<LETTER>>> cycleTraces;

		final Map<IcfgLocation, List<Integer>> withoutNestedCycles = new HashMap<>(possibleCycles);
		for (final IcfgLocation nestedHead : nestedCycles) {
			withoutNestedCycles.remove(nestedHead);
		}
		cycleTraces = cyclePaths(withoutNestedCycles);
		return cycleTraces;
	}

	/**
	 * Transform an interval into statements of the trace.
	 *
	 * @param possibleCycles
	 * @return
	 */
	private Map<IcfgLocation, Set<List<LETTER>>> cyclePaths(final Map<IcfgLocation, List<Integer>> cycles) {
		final Map<IcfgLocation, Set<List<LETTER>>> cycleTransitions = new HashMap<>();
		for (final Entry<IcfgLocation, List<Integer>> cycle : cycles.entrySet()) {
			final Set<List<LETTER>> statements = new HashSet<>();
			final IcfgLocation loopHead = cycle.getKey();
			int i = 1;
			while (i < cycle.getValue().size()) {
				final List<LETTER> trace =
						new ArrayList<>(mTrace.subList(cycle.getValue().get(i - 1), cycle.getValue().get(i)));
				statements.add(trace);
				i++;
			}
			cycleTransitions.put(loopHead, statements);
		}
		return cycleTransitions;
	}

	/**
	 * Given a list of cycles with their respective repetition locations, check what kind of cycle each are: There are 2
	 * kind of cycles: 1: Disjunct -> They do not intersect, meaning there is a gap between the last repetition location
	 * of one cycle with the first repetition of the other 2: Nested -> Two loops are nested if the interval of
	 * repetitions of one loop lie within the interval of the other.
	 *
	 * We do not need nested loops.
	 *
	 * @param cyclesWithNested
	 *            List of cycles that are possibly nested
	 * @return
	 */
	private Set<IcfgLocation> getNestedCycles(final Map<IcfgLocation, List<Integer>> cyclesWithNested) {
		final Set<IcfgLocation> nestedCycles = new HashSet<>();
		for (final Iterator<Map.Entry<IcfgLocation, List<Integer>>> cycles =
				cyclesWithNested.entrySet().iterator(); cycles.hasNext();) {
			final Map.Entry<IcfgLocation, List<Integer>> cycle = cycles.next();
			final IcfgLocation loopHead = cycle.getKey();
			final int firstOccurence = cycle.getValue().get(0);
			final int lastOccurence = cycle.getValue().get(cycle.getValue().size() - 1);

			for (final Iterator<Map.Entry<IcfgLocation, List<Integer>>> otherCycles =
					cyclesWithNested.entrySet().iterator(); otherCycles.hasNext();) {
				final Map.Entry<IcfgLocation, List<Integer>> otherCycle = otherCycles.next();
				final IcfgLocation loopHeadOther = otherCycle.getKey();
				final int firstOccurenceOther = otherCycle.getValue().get(0);
				final int lastOccurenceOther = otherCycle.getValue().get(otherCycle.getValue().size() - 1);
				if (loopHead != loopHeadOther
						&& (firstOccurence < firstOccurenceOther && lastOccurence > lastOccurenceOther)) {
					nestedCycles.add(loopHeadOther);
				}
			}
		}
		return nestedCycles;
	}

	public void setTrace(final List<LETTER> trace) {
		mTrace = trace;
	}

	public List<LETTER> getTrace() {
		return mTrace;
	}

	public List<IcfgLocation> getTraceLocations() {
		return mTraceLocations;
	}
}
