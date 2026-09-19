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

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

final class MayActiveThreadAnalysis {

	private MayActiveThreadAnalysis() {
	}

	static ThreadActivity compute(final IIcfg<IcfgLocation> icfg, final Set<String> threadIds,
			final ThreadForkGraph forkGraph) {
		final Map<IcfgLocation, Set<String>> activeThreadsByLocation = new HashMap<>();
		final Set<String> selfForkingThreads = new HashSet<>();
		final ArrayDeque<IcfgLocation> pendingLocations = new ArrayDeque<>();

		for (final IcfgLocation initial : icfg.getInitialNodes()) {
			activeThreadsByLocation.put(initial, new HashSet<>(Set.of(initial.getProcedure())));
			pendingLocations.add(initial);
		}
		while (!pendingLocations.isEmpty()) {
			final IcfgLocation source = pendingLocations.removeFirst();
			final Set<String> activeAtSource = activeThreadsByLocation.get(source);

			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				final IcfgLocation target = edge.getTarget();
				if (target == null) {
					continue;
				}

				final String forkedThread = ThreadForkGraph.getForkedThread(edge);
				Set<String> activeAfterEdge = activeAtSource;
				if (forkedThread != null) {
					if (activeAtSource.contains(forkedThread)) {
						selfForkingThreads.add(forkedThread);
					}
					activeAfterEdge = new HashSet<>(activeAtSource);
					activeAfterEdge.add(forkedThread);

					final IcfgLocation forkedEntry = icfg.getProcedureEntryNodes().get(forkedThread);
					propagate(activeThreadsByLocation, pendingLocations, forkedEntry, activeAfterEdge);
				}

				propagate(activeThreadsByLocation, pendingLocations, target, activeAfterEdge);
			}
		}

		return new ThreadActivity(closeUnderNestedForks(activeThreadsByLocation, threadIds, forkGraph, selfForkingThreads),
				Set.copyOf(selfForkingThreads));
	}

	private static Map<IcfgLocation, Set<String>> closeUnderNestedForks(
			final Map<IcfgLocation, Set<String>> activeThreadsByLocation, final Set<String> threadIds,
			final ThreadForkGraph forkGraph, final Set<String> selfForkingThreads) {
		final Map<IcfgLocation, Set<String>> finalizedActiveThreads = new HashMap<>();
		for (final var entry : activeThreadsByLocation.entrySet()) {
			final IcfgLocation location = entry.getKey();
			final String ownerThread = location.getProcedure();
			final Set<String> activeThreads = restrictToConfiguredThreads(entry.getValue(), threadIds);
			final Set<String> closedActiveThreads = new HashSet<>(activeThreads);
			for (final String activeThread : activeThreads) {
				if (activeThread.equals(ownerThread) && !selfForkingThreads.contains(ownerThread)) {
					continue;
				}
				closedActiveThreads.addAll(forkGraph.getMayForkThreads(activeThread));
			}
			if (!activeThreads.isEmpty()) {
				finalizedActiveThreads.put(location, Set.copyOf(closedActiveThreads));
			}
		}
		return Map.copyOf(finalizedActiveThreads);
	}

	private static Set<String> restrictToConfiguredThreads(final Set<String> threads, final Set<String> threadIds) {
		final Set<String> restrictedThreads = new HashSet<>(threads);
		restrictedThreads.retainAll(threadIds);
		return restrictedThreads;
	}

	private static void propagate(final Map<IcfgLocation, Set<String>> active, final ArrayDeque<IcfgLocation> worklist,
			final IcfgLocation target, final Set<String> transferredActiveThreads) {
		if (target == null) {
			return;
		}
		final Set<String> existing = active.get(target);
		if (existing == null) {
			active.put(target, new HashSet<>(transferredActiveThreads));
			worklist.add(target);
		} else if (existing.addAll(transferredActiveThreads)) {
			worklist.add(target);
		}
	}

	static record ThreadActivity(Map<IcfgLocation, Set<String>> activeByLocation, Set<String> selfForkingThreads) {
	}
}
