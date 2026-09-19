/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.threadactivity;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.threadactivity.MayActiveThreadAnalysis.ThreadActivity;

/**
 * Computes the threads that may be active at each location and, when requested, the threads that have definitely
 * been joined.
 */
public final class ThreadActivityPreanalysis {

	private final Map<IcfgLocation, Set<String>> mActiveByLocation;
	private final Map<IcfgLocation, Set<String>> mDefinitelyJoinedByLocation;
	private final Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, String> mJoinedThreadByJoin;
	private final Set<String> mMultiForkedThreads;

	private ThreadActivityPreanalysis(final Map<IcfgLocation, Set<String>> activeByLocation,
			final Map<IcfgLocation, Set<String>> definitelyJoinedByLocation,
			final Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, String> joinedThreadByJoin,
			final Set<String> multiForkedThreads) {
		mActiveByLocation = Map.copyOf(activeByLocation);
		mDefinitelyJoinedByLocation = Map.copyOf(definitelyJoinedByLocation);
		mJoinedThreadByJoin = Map.copyOf(joinedThreadByJoin);
		mMultiForkedThreads = Set.copyOf(multiForkedThreads);
	}

	public static ThreadActivityPreanalysis compute(final IIcfg<IcfgLocation> icfg, final Set<String> threadIds,
			final boolean enableJoinPrecision) {
		final ThreadForkGraph forkGraph = ThreadForkGraph.compute(icfg, threadIds);
		final ThreadActivity active = MayActiveThreadAnalysis.compute(icfg, threadIds, forkGraph);
		final Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, String> joinedThreadByJoin = enableJoinPrecision
				? DefinitelyJoinedThreadAnalysis.computeTrackedJoins(icfg, threadIds, active.selfForkingThreads())
				: Map.of();
		final Map<IcfgLocation, Set<String>> definitelyJoinedByLocation = joinedThreadByJoin.isEmpty() ? Map.of()
				: DefinitelyJoinedThreadAnalysis.computeDefinitelyJoinedByLocation(icfg, joinedThreadByJoin);
		return new ThreadActivityPreanalysis(active.activeByLocation(), definitelyJoinedByLocation, joinedThreadByJoin,
				active.selfForkingThreads());
	}

	/**
	 * Matches each join transition to the forked procedure whose fork-id arguments it joins on. Pass null threadIds
	 * to match against every forked procedure.
	 */
	public static Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, String> matchJoinsToThreads(
			final IIcfg<IcfgLocation> icfg, final Set<String> threadIds) {
		return DefinitelyJoinedThreadAnalysis.matchJoinsToThreads(icfg, threadIds);
	}

	public Set<String> getActiveThreadsAt(final IcfgLocation location) {
		if (location == null) {
			return Set.of();
		}
		final Set<String> result = mActiveByLocation.get(location);
		return result != null ? result : Set.of();
	}

	public boolean mayBeActiveAt(final IcfgLocation location, final String threadId) {
		if (location == null) {
			return true;
		}
		final Set<String> result = mActiveByLocation.get(location);
		return result == null || result.contains(threadId);
	}

	public boolean isDefinitelyJoinedAt(final IcfgLocation location, final String threadId) {
		if (location == null) {
			return false;
		}
		final Set<String> result = mDefinitelyJoinedByLocation.get(location);
		return result != null && result.contains(threadId);
	}

	public String getJoinedThreadForJoin(final IIcfgJoinTransitionThreadCurrent<IcfgLocation> join) {
		return mJoinedThreadByJoin.get(join);
	}

	public Set<String> getMultiForkedThreads() {
		return mMultiForkedThreads;
	}
}
