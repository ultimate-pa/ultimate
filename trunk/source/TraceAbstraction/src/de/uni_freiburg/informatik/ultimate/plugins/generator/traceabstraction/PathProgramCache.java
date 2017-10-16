/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * {@link PathProgramCache} saves a hash of the trace and the path program that is analyzed in each iteration.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class PathProgramCache<LETTER> {

	private final ILogger mLogger;
	private final Map<Set<LETTER>, Integer> mKnownPathPrograms;
	private final List<Integer> mTraceHashes;

	public PathProgramCache(final ILogger logger) {
		mLogger = logger;
		mKnownPathPrograms = new HashMap<>();
		mTraceHashes = new ArrayList<>();
	}

	/**
	 * Add the currently analyzed counterexample to the {@link PathProgramCache} and receive the number of times the
	 * path program induced by this counterexample has already been added (including this time).
	 *
	 * Note that the path program is relative to the original program, not the current abstraction.
	 *
	 * @param counterexample
	 *            The counterexample you want to cache.
	 * @return The number of times the path program induced by this counterexample has already been added (will be > 0).
	 */
	public int addRun(final IRun<LETTER, ?, ?> counterexample) {
		final List<LETTER> trace = counterexample.getWord().asList();
		final int traceHash = trace.hashCode();
		mTraceHashes.add(traceHash);

		final Set<LETTER> pathProgramRepresentative = new HashSet<>(trace);
		final Integer count = mKnownPathPrograms.get(pathProgramRepresentative);
		final int rtr;
		if (count == null) {
			rtr = 1;
		} else {
			rtr = count.intValue() + 1;
		}
		mKnownPathPrograms.put(pathProgramRepresentative, rtr);

		mLogger.info(
				"Analyzing trace with hash " + traceHash + ", now seen corresponding path program " + rtr + " times");

		return rtr;
	}

	/**
	 *
	 * @return The number of times the path program induced by the supplied counterexample has already been added.
	 */
	public int getPathProgramCount(final IRun<LETTER, ?, ?> counterexample) {
		final Set<LETTER> pathProgramRepresentative = counterexample.getWord().asSet();
		final Integer count = mKnownPathPrograms.get(pathProgramRepresentative);
		if (count == null) {
			mLogger.warn("You did not report this counterexample before!");
			return 0;
		}
		return count.intValue();
	}

}
