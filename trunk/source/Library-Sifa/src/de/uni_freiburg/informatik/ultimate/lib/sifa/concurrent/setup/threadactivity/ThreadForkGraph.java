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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * The threads that each configured thread may create, directly or through nested forks.
 */
final class ThreadForkGraph {

	private final Map<String, Set<String>> mMayForkThreads;

	private ThreadForkGraph(final Map<String, Set<String>> mayForkThreads) {
		mMayForkThreads = Map.copyOf(mayForkThreads);
	}

	static ThreadForkGraph compute(final IIcfg<IcfgLocation> icfg, final Set<String> threadIds) {
		final Map<String, Set<String>> directForkChildrenByThread = new HashMap<>();
		for (final var programPoints : icfg.getProgramPoints().entrySet()) {
			final String threadId = programPoints.getKey();
			for (final IcfgLocation location : programPoints.getValue().values()) {
				for (final IcfgEdge edge : location.getOutgoingEdges()) {
					final String forkedThread = getForkedThread(edge);
					if (forkedThread != null) {
						directForkChildrenByThread.computeIfAbsent(threadId, ignored -> new HashSet<>())
								.add(forkedThread);
					}
				}
			}
		}

		final Set<String> candidateThreads = new HashSet<>(icfg.getProgramPoints().keySet());
		candidateThreads.addAll(directForkChildrenByThread.keySet());
		candidateThreads.retainAll(threadIds);

		final Map<String, Set<String>> mayForkThreads = new HashMap<>();
		for (final String threadId : candidateThreads) {
			mayForkThreads.put(threadId, computeMayForkThreads(threadId, directForkChildrenByThread, threadIds));
		}
		return new ThreadForkGraph(mayForkThreads);
	}

	private static Set<String> computeMayForkThreads(final String threadId,
			final Map<String, Set<String>> directForkChildrenByThread, final Set<String> threadIds) {
		final Set<String> mayForkThreads = new HashSet<>();
		final ArrayDeque<String> pendingForkThreads = new ArrayDeque<>(
				directForkChildrenByThread.getOrDefault(threadId, Set.of()));
		while (!pendingForkThreads.isEmpty()) {
			final String forkThread = pendingForkThreads.removeFirst();
			if (!mayForkThreads.add(forkThread)) {
				continue;
			}
			pendingForkThreads.addAll(directForkChildrenByThread.getOrDefault(forkThread, Set.of()));
		}
		mayForkThreads.retainAll(threadIds);
		return Set.copyOf(mayForkThreads);
	}

	Set<String> getMayForkThreads(final String threadId) {
		return mMayForkThreads.getOrDefault(threadId, Set.of());
	}

	static String getForkedThread(final IcfgEdge edge) {
		if (edge instanceof final IIcfgForkTransitionThreadCurrent<?> fork) {
			return fork.getNameOfForkedProcedure();
		}
		if (edge instanceof final IIcfgForkTransitionThreadOther<?> forkOther) {
			final var corresponding = forkOther.getCorrespondingIIcfgForkTransitionCurrentThread();
			return corresponding != null ? corresponding.getNameOfForkedProcedure() : null;
		}
		return null;
	}
}
