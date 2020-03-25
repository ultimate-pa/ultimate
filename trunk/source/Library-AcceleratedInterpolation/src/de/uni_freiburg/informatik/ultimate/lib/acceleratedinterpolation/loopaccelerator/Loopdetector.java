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

package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.loopaccelerator;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.AcceleratedInterpolation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de) This class represents the loop detector needed for
 *         {@link AcceleratedInterpolation}
 */
public class Loopdetector<LETTER extends IIcfgTransition<?>> {

	private List<LETTER> mTrace;
	private final List<IcfgLocation> mTraceLocations;
	private final ILogger mLogger;

	public Loopdetector(final List<LETTER> trace, final ILogger logger) {
		mLogger = logger;
		mTrace = trace;
		mTraceLocations = statementsToLocations(trace);

		mLogger.debug("Loopdetector created.");
	}

	public void getLoop() {
		final Set<IcfgLocation> possLoopHeads = new HashSet<>();
		final Set<Pair<IcfgLocation, Integer>> locFirstSeen = new HashSet<>();
		final Set<Pair<IcfgLocation, Integer>> loopHeads = new HashSet<>();

		int i = 0;
		for (final IcfgLocation loc : mTraceLocations) {
			if (!possLoopHeads.add(loc)) {
				loopHeads.add(new Pair<>(loc, i));
			} else {
				locFirstSeen.add(new Pair<>(loc, i));
			}
			i++;
		}
		if (loopHeads.isEmpty()) {
			mLogger.debug("Found no loopheads in trace!" + mTrace);
			return;
		} else {
			mLogger.debug("found possible Loopheads" + loopHeads);
		}
	}

	private List<IcfgLocation> statementsToLocations(final List<LETTER> trace) {
		final List<IcfgLocation> traceLocations = new ArrayList<>();

		for (final LETTER stm : trace) {
			traceLocations.add(stm.getSource());
		}
		return traceLocations;
	}

	/**
	 * Get a given loop's transitions
	 *
	 * TODO: This extracts the smallest repetition of the first loop of loopHead; in particular, this extracts only one
	 * loop per loop head
	 *
	 * @param loopHead
	 *            beginning of the loop
	 *
	 * @return body of the loop
	 */
	public List<LETTER> getLoopNaive(final IcfgLocation loopHead, final List<LETTER> trace) {
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
