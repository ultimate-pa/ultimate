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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.logic.Term;

final class DefinitelyJoinedThreadAnalysis {

	private DefinitelyJoinedThreadAnalysis() {
	}

	static Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, String> computeTrackedJoins(
			final IIcfg<IcfgLocation> icfg, final Set<String> threadIds, final Set<String> selfForkingThreads) {
		final Map<String, Integer> forkCount = new HashMap<>();
		for (final var fork : icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().keySet()) {
			final String threadId = fork.getNameOfForkedProcedure();
			if (threadIds.contains(threadId)) {
				forkCount.merge(threadId, 1, Integer::sum);
			}
		}
		final Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, String> candidates = new LinkedHashMap<>(
				matchJoinsToThreads(icfg, threadIds));
		final Map<String, Integer> joinCount = new HashMap<>();
		candidates.values().forEach(threadId -> joinCount.merge(threadId, 1, Integer::sum));
		candidates.entrySet().removeIf(entry -> forkCount.getOrDefault(entry.getValue(), 0) != 1
				|| joinCount.getOrDefault(entry.getValue(), 0) != 1
				|| selfForkingThreads.contains(entry.getValue()));
		return Map.copyOf(candidates);
	}

	static Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, String> matchJoinsToThreads(
			final IIcfg<IcfgLocation> icfg, final Set<String> threadIds) {
		final var concurrency = icfg.getCfgSmtToolkit().getConcurrencyInformation();
		final Map<List<Term>, String> threadByForkId = new LinkedHashMap<>();
		for (final var fork : concurrency.getThreadInstanceMap().keySet()) {
			final String threadId = fork.getNameOfForkedProcedure();
			if (threadIds != null && !threadIds.contains(threadId)) {
				continue;
			}
			threadByForkId.putIfAbsent(List.of(fork.getForkSmtArguments().getThreadIdArguments().terms()), threadId);
		}
		final Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, String> matched = new LinkedHashMap<>();
		for (final var join : concurrency.getJoinTransitions()) {
			final String threadId = threadByForkId
					.get(List.of(join.getJoinSmtArguments().getThreadIdArguments().terms()));
			if (threadId != null) {
				matched.put(join, threadId);
			}
		}
		return matched;
	}

	static Map<IcfgLocation, Set<String>> computeDefinitelyJoinedByLocation(final IIcfg<IcfgLocation> icfg,
			final Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, String> joinedThreadByJoin) {
		final Map<IcfgLocation, Set<String>> definitelyJoinedByLocation = new HashMap<>();
		final ArrayDeque<IcfgLocation> pendingLocations = new ArrayDeque<>();
		for (final IcfgLocation entry : icfg.getProcedureEntryNodes().values()) {
			definitelyJoinedByLocation.put(entry, new HashSet<>());
			pendingLocations.add(entry);
		}

		while (!pendingLocations.isEmpty()) {
			final IcfgLocation source = pendingLocations.removeFirst();
			final Set<String> joinedAtSource = definitelyJoinedByLocation.get(source);

			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				if (isCrossThreadEdge(edge)) {
					continue;
				}
				final IcfgLocation target = edge.getTarget();
				if (target == null) {
					continue;
				}

				final Set<String> joinedAfterEdge = updatedJoinedSet(joinedAtSource, edge, joinedThreadByJoin);
				propagateMust(definitelyJoinedByLocation, pendingLocations, target, joinedAfterEdge);
			}
		}

		final Map<IcfgLocation, Set<String>> finalized = new HashMap<>();
		for (final var entry : definitelyJoinedByLocation.entrySet()) {
			if (!entry.getValue().isEmpty()) {
				finalized.put(entry.getKey(), Set.copyOf(entry.getValue()));
			}
		}
		return Map.copyOf(finalized);
	}

	private static Set<String> updatedJoinedSet(final Set<String> before, final IcfgEdge edge,
			final Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, String> joinedThreadByJoin) {
		Set<String> result = before;
		if (edge instanceof final IIcfgForkTransitionThreadCurrent<?> fork
				&& before.contains(fork.getNameOfForkedProcedure())) {
			result = new HashSet<>(before);
			result.remove(fork.getNameOfForkedProcedure());
		}
		if (edge instanceof final IIcfgJoinTransitionThreadCurrent<?> join) {
			final String joinedThread = joinedThreadByJoin.get(join);
			if (joinedThread != null && !result.contains(joinedThread)) {
				if (result == before) {
					result = new HashSet<>(before);
				}
				result.add(joinedThread);
			}
		}
		return result;
	}

	private static void propagateMust(final Map<IcfgLocation, Set<String>> factsByLocation,
			final ArrayDeque<IcfgLocation> worklist, final IcfgLocation target, final Set<String> transferredFacts) {
		final Set<String> existing = factsByLocation.get(target);
		if (existing == null) {
			factsByLocation.put(target, new HashSet<>(transferredFacts));
			worklist.add(target);
			return;
		}
		final Set<String> intersection = new HashSet<>(existing);
		intersection.retainAll(transferredFacts);
		if (!existing.equals(intersection)) {
			factsByLocation.put(target, intersection);
			worklist.add(target);
		}
	}

	private static boolean isCrossThreadEdge(final IcfgEdge edge) {
		return edge instanceof IIcfgForkTransitionThreadOther<?> || edge instanceof IIcfgJoinTransitionThreadOther<?>;
	}
}
