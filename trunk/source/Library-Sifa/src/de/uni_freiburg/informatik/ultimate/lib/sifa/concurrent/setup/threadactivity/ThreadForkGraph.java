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
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public final class ThreadForkGraph {
	public static final String MAIN_THREAD = "ULTIMATE.start";

	private final List<String> mThreadIds;
	private final Map<String, List<IIcfgForkTransitionThreadCurrent<IcfgLocation>>> mForksByThread;
	private final Map<String, Set<IcfgLocation>> mForkSourcesByThread;
	private final Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, String> mMatchedJoins;
	private final Map<String, Set<String>> mMayForkThreads;

	private ThreadForkGraph(final List<String> threadIds,
			final Map<String, List<IIcfgForkTransitionThreadCurrent<IcfgLocation>>> forksByThread,
			final Map<String, Set<IcfgLocation>> forkSourcesByThread,
			final Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, String> matchedJoins,
			final Map<String, Set<String>> mayForkThreads) {
		mThreadIds = List.copyOf(threadIds);
		forksByThread.replaceAll((thread, forks) -> List.copyOf(forks));
		mForksByThread = Collections.unmodifiableMap(new LinkedHashMap<>(forksByThread));
		forkSourcesByThread.replaceAll((thread, sources) -> Collections.unmodifiableSet(new LinkedHashSet<>(sources)));
		mForkSourcesByThread = Map.copyOf(forkSourcesByThread);
		mMatchedJoins = Collections.unmodifiableMap(new LinkedHashMap<>(matchedJoins));
		mMayForkThreads = Map.copyOf(mayForkThreads);
	}

	public static ThreadForkGraph compute(final IIcfg<IcfgLocation> icfg) {
		final var concurrency = icfg.getCfgSmtToolkit().getConcurrencyInformation();
		final Map<String, List<IIcfgForkTransitionThreadCurrent<IcfgLocation>>> forksByThread = new LinkedHashMap<>();
		final Map<String, Set<String>> forkTargetsByThread = new LinkedHashMap<>();
		final Map<List<Term>, String> threadByForkId = new LinkedHashMap<>();
		for (final var fork : concurrency.getThreadInstanceMap().keySet()) {
			final String threadId = fork.getNameOfForkedProcedure();
			forksByThread.computeIfAbsent(threadId, ignored -> new ArrayList<>()).add(fork);
			forkTargetsByThread.computeIfAbsent(fork.getSource().getProcedure(), ignored -> new LinkedHashSet<>())
					.add(threadId);
			threadByForkId.putIfAbsent(List.of(fork.getForkSmtArguments().getThreadIdArguments().terms()), threadId);
		}
		final List<String> threadIds = discoverThreadIds(forkTargetsByThread, forksByThread.keySet());
		final Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, String> matchedJoins = new LinkedHashMap<>();
		for (final var join : concurrency.getJoinTransitions()) {
			final String threadId =
					threadByForkId.get(List.of(join.getJoinSmtArguments().getThreadIdArguments().terms()));
			if (threadId != null) {
				matchedJoins.put(join, threadId);
			}
		}

		final Map<String, Set<String>> directForkChildrenByThread = new HashMap<>();
		final Map<String, Set<IcfgLocation>> forkSourcesByThread = new LinkedHashMap<>();
		for (final var programPoints : icfg.getProgramPoints().entrySet()) {
			final String threadId = programPoints.getKey();
			for (final IcfgLocation location : programPoints.getValue().values()) {
				for (final IcfgEdge edge : location.getOutgoingEdges()) {
					if (edge instanceof IIcfgForkTransitionThreadCurrent<?>) {
						forkSourcesByThread.computeIfAbsent(location.getProcedure(), ignored -> new LinkedHashSet<>())
								.add(location);
					}
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
		final Set<String> configuredThreads = Set.copyOf(threadIds);
		candidateThreads.retainAll(configuredThreads);
		final Map<String, Set<String>> mayForkThreads = new HashMap<>();
		for (final String threadId : candidateThreads) {
			mayForkThreads.put(threadId,
					computeMayForkThreads(threadId, directForkChildrenByThread, configuredThreads));
		}
		return new ThreadForkGraph(threadIds, forksByThread, forkSourcesByThread, matchedJoins, mayForkThreads);
	}

	public List<String> getThreadIds() {
		return mThreadIds;
	}

	public List<IIcfgForkTransitionThreadCurrent<IcfgLocation>> getForksForThread(final String threadId) {
		return mForksByThread.getOrDefault(threadId, List.of());
	}

	public Set<IcfgLocation> getForkSources(final String threadId) {
		return mForkSourcesByThread.getOrDefault(threadId, Set.of());
	}

	public Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, String> getMatchedJoins() {
		return mMatchedJoins;
	}

	public Map<String, Set<IcfgLocation>> computePreForkSourcesByThread(final IIcfg<IcfgLocation> icfg,
			final Set<String> multiForkedThreads) {
		final Map<String, Set<IcfgLocation>> result = new LinkedHashMap<>();
		for (final var entry : mForksByThread.entrySet()) {
			if (entry.getValue().size() != 1) {
				continue;
			}
			final IIcfgForkTransitionThreadCurrent<IcfgLocation> fork = entry.getValue().get(0);
			final IcfgLocation forkSource = fork.getSource();
			final IcfgLocation forkTarget = fork.getTarget();
			if (forkSource == null || forkTarget == null || multiForkedThreads.contains(forkSource.getProcedure())) {
				continue;
			}
			final Set<IcfgLocation> reachableAfterFork = reachableSameProcedure(forkTarget, false);
			final Set<IcfgLocation> reachesFork = reachableSameProcedure(forkSource, true);
			final Set<IcfgLocation> preForkSources = new LinkedHashSet<>();
			for (final IcfgLocation candidate : icfg.getProgramPoints()
					.getOrDefault(forkSource.getProcedure(), Map.of()).values()) {
				if (reachesFork.contains(candidate) && !reachableAfterFork.contains(candidate)) {
					preForkSources.add(candidate);
				}
			}
			if (!preForkSources.isEmpty()) {
				result.put(entry.getKey(), Set.copyOf(preForkSources));
			}
		}
		return Map.copyOf(result);
	}

	private static Set<IcfgLocation> reachableSameProcedure(final IcfgLocation start, final boolean backwards) {
		final Set<IcfgLocation> result = new LinkedHashSet<>();
		final ArrayDeque<IcfgLocation> pending = new ArrayDeque<>();
		result.add(start);
		pending.add(start);
		while (!pending.isEmpty()) {
			final IcfgLocation location = pending.removeFirst();
			for (final IcfgEdge edge : backwards ? location.getIncomingEdges() : location.getOutgoingEdges()) {
				final IcfgLocation next = backwards ? edge.getSource() : edge.getTarget();
				if (next == null || !start.getProcedure().equals(next.getProcedure()) || !result.add(next)) {
					continue;
				}
				pending.add(next);
			}
		}
		return result;
	}

	private static List<String> discoverThreadIds(final Map<String, Set<String>> forksByThread,
			final Set<String> forkedThreads) {
		final List<String> ordered = new ArrayList<>();
		final Set<String> visited = new LinkedHashSet<>();
		ordered.add(MAIN_THREAD);
		visited.add(MAIN_THREAD);
		for (int i = 0; i < ordered.size(); i++) {
			for (final String child : forksByThread.getOrDefault(ordered.get(i), Set.of())) {
				if (visited.add(child)) {
					ordered.add(child);
				}
			}
		}
		forkedThreads.stream().filter(visited::add).forEach(ordered::add);
		return ordered;
	}

	private static Set<String> computeMayForkThreads(final String threadId,
			final Map<String, Set<String>> directForkChildrenByThread, final Set<String> threadIds) {
		final Set<String> mayForkThreads = new HashSet<>();
		final ArrayDeque<String> pendingForkThreads =
				new ArrayDeque<>(directForkChildrenByThread.getOrDefault(threadId, Set.of()));
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
