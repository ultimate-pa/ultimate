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
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.MustLocksetAnalysis;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

public class LocationAbstraction {
	private record LocationKey(int groupId, Set<String> lockset) {
	}

	private final Map<String, Integer> mNextLocationIdByThread = new HashMap<>();
	private final Map<String, Map<LocationKey, Integer>> mLocationIdsByThread = new HashMap<>();
	private final Map<IcfgLocation, Integer> mLocationIds = new HashMap<>();

	public Map<IcfgLocation, Integer> computeLocationAbstraction(final LocationAbstractionType type,
			final IIcfg<IcfgLocation> icfg, final MustLocksetAnalysis locksetInfo) {
		return switch (type) {
		case SINGLETON -> assignLocationIds(l -> 0, icfg);
		case SPLIT_AT_NONLOCK_GUARDS_WRITES_AND_LOCKSETS -> {
			final Map<IcfgLocation, Integer> groupIds = groupLocations(icfg, locksetInfo.getLockVars());
			yield assignLocationIds(l -> getLocationId(l, groupIds, locksetInfo), icfg);
		}
		case SPLIT_AT_EVERY_LOCATION -> assignLocationIds(
				l -> mLocationIds.computeIfAbsent(l, __ -> nextLocationId(l.getProcedure())), icfg);
		};
	}

	/**
	 * We put some program locations in the same group to reduce the number of locations the analysis has to track.
	 * The points before and after a statement share a group when the statement only uses local variables or mutexes.
	 * For example, incrementing a local counter does not need a separate location.
	 * We do not combine groups for statements that start another thread or access other shared variables.
	 */
	private static Map<IcfgLocation, Integer> groupLocations(final IIcfg<IcfgLocation> icfg,
			final Set<IProgramVar> lockVars) {
		final var locations = new IcfgLocationIterator<>(icfg.getProcedureEntryNodes().values()).asStream().toList();
		final UnionFind<IcfgLocation> groups = new UnionFind<>();
		locations.forEach(groups::makeEquivalenceClass);
		for (final IcfgLocation source : locations) {
			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				final IcfgLocation target = edge.getTarget();
				if (canGroupLocations(edge, lockVars)) {
					groups.union(source, target);
				}
			}
		}
		final Map<String, Map<IcfgLocation, Integer>> idsByThread = new HashMap<>();
		final Map<IcfgLocation, Integer> result = new LinkedHashMap<>();
		for (final IcfgLocation location : locations) {
			final Map<IcfgLocation, Integer> ids =
					idsByThread.computeIfAbsent(location.getProcedure(), ignored -> new HashMap<>());
			result.put(location, ids.computeIfAbsent(groups.find(location), ignored -> ids.size() + 1));
		}
		return result;
	}

	private static boolean canGroupLocations(final IcfgEdge edge, final Set<IProgramVar> lockVars) {
		return edge.getSource().getProcedure().equals(edge.getTarget().getProcedure())
				&& !(edge instanceof IIcfgForkTransitionThreadCurrent<?>)
				&& lockVars.containsAll(InterferenceUtils.getReferencedGlobals(edge.getTransformula()));
	}

	private Map<IcfgLocation, Integer> assignLocationIds(final Function<IcfgLocation, Integer> mappingFunction,
			final IIcfg<IcfgLocation> icfg) {
		final Map<IcfgLocation, Integer> result = new LinkedHashMap<>();
		for (final IcfgLocation entryLoc : icfg.getProcedureEntryNodes().values()) {
			final IcfgLocationIterator<IcfgLocation> iter = new IcfgLocationIterator<>(entryLoc);
			while (iter.hasNext()) {
				result.computeIfAbsent(iter.next(), mappingFunction);
			}
		}
		return result;
	}

	private int getLocationId(final IcfgLocation location, final Map<IcfgLocation, Integer> groupIds,
			final MustLocksetAnalysis locksetInfo) {
		final LocationKey key = new LocationKey(groupIds.get(location), locksetInfo.mustLocksetAt(location));
		final Map<LocationKey, Integer> ids =
				mLocationIdsByThread.computeIfAbsent(location.getProcedure(), ignored -> new HashMap<>());
		return ids.computeIfAbsent(key, ignored -> nextLocationId(location.getProcedure()));
	}

	private int nextLocationId(final String thread) {
		final int counter = mNextLocationIdByThread.getOrDefault(thread, 1);
		mNextLocationIdByThread.put(thread, counter + 1);
		return counter;
	}
}
