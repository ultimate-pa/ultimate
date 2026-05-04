package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup;

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

/*
 * Currently a preanalysis computing for each location which other threads can be active.
 * (replaces/acts as threadcounter ghostvariables in states from theory)
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
		mActiveByLocation = activeByLocation;
		mDefinitelyJoinedByLocation = definitelyJoinedByLocation;
		mJoinedThreadByJoin = joinedThreadByJoin;
		mMultiForkedThreads = multiForkedThreads;
	}

	public static ThreadActivityPreanalysis compute(final IIcfg<IcfgLocation> icfg, final Set<String> threadIds,
			final boolean enableJoinPrecision) {
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

				final String forkedThread = getForkedThread(edge);
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

		final Map<String, Set<String>> forkReachabilityByThread = computeForkReachabilityByThread(icfg, threadIds);
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
				closedActiveThreads.addAll(forkReachabilityByThread.getOrDefault(activeThread, Set.of()));
			}
			if (!activeThreads.isEmpty()) {
				finalizedActiveThreads.put(entry.getKey(), Set.copyOf(closedActiveThreads));
			}
		}
		final Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, String> joinedThreadByJoin = enableJoinPrecision
				? computeTrackedJoinMap(icfg, threadIds, selfForkingThreads)
				: Map.of();
		final Map<IcfgLocation, Set<String>> definitelyJoinedByLocation =
				joinedThreadByJoin.isEmpty() ? Map.of() : computeDefinitelyJoinedByLocation(icfg, joinedThreadByJoin);
		return new ThreadActivityPreanalysis(Map.copyOf(finalizedActiveThreads), Map.copyOf(definitelyJoinedByLocation),
				Map.copyOf(joinedThreadByJoin), Set.copyOf(selfForkingThreads));
	}

	private static Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, String> computeTrackedJoinMap(
			final IIcfg<IcfgLocation> icfg, final Set<String> threadIds, final Set<String> selfForkingThreads) {
		final Set<String> trackedThreads = identifyUniquelyJoinTrackedThreads(icfg, threadIds, selfForkingThreads);
		return trackedThreads.isEmpty() ? Map.of() : buildTrackedJoinMap(icfg, trackedThreads);
	}

	private static Map<IcfgLocation, Set<String>> computeDefinitelyJoinedByLocation(final IIcfg<IcfgLocation> icfg,
			final Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, String> joinedThreadByJoin) {
		if (joinedThreadByJoin.isEmpty()) {
			return Map.of();
		}
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

				Set<String> joinedAfterEdge = joinedAtSource;
				if (edge instanceof final IIcfgForkTransitionThreadCurrent<?> forkCurrent) {
					final String forkedThread = forkCurrent.getNameOfForkedProcedure();
					if (joinedAtSource.contains(forkedThread)) {
						joinedAfterEdge = new HashSet<>(joinedAtSource);
						joinedAfterEdge.remove(forkedThread);
					}
				}
				if (edge instanceof IIcfgJoinTransitionThreadCurrent<?>) {
					@SuppressWarnings("unchecked")
					final IIcfgJoinTransitionThreadCurrent<IcfgLocation> joinCurrent =
							(IIcfgJoinTransitionThreadCurrent<IcfgLocation>) edge;
					final String joinedThread = joinedThreadByJoin.get(joinCurrent);
					if (joinedThread != null && !joinedAfterEdge.contains(joinedThread)) {
						if (joinedAfterEdge == joinedAtSource) {
							joinedAfterEdge = new HashSet<>(joinedAtSource);
						}
						joinedAfterEdge.add(joinedThread);
					}
				}
				propagateMust(definitelyJoinedByLocation, pendingLocations, target, joinedAfterEdge);
			}
		}

		final Map<IcfgLocation, Set<String>> finalized = new HashMap<>();
		for (final var entry : definitelyJoinedByLocation.entrySet()) {
			if (!entry.getValue().isEmpty()) {
				finalized.put(entry.getKey(), Set.copyOf(entry.getValue()));
			}
		}
		return finalized;
	}

	private static Set<String> identifyUniquelyJoinTrackedThreads(final IIcfg<IcfgLocation> icfg,
			final Set<String> threadIds, final Set<String> selfForkingThreads) {
		final var concurrency = icfg.getCfgSmtToolkit().getConcurrencyInformation();
		final Map<List<Term>, String> threadByForkId = new LinkedHashMap<>();
		final Map<String, Integer> forkCountByThread = new HashMap<>();
		for (final var fork : concurrency.getThreadInstanceMap().keySet()) {
			final String threadId = fork.getNameOfForkedProcedure();
			if (threadIds != null && !threadIds.contains(threadId)) {
				continue;
			}
			threadByForkId.put(List.of(fork.getForkSmtArguments().getThreadIdArguments().terms()), threadId);
			forkCountByThread.merge(threadId, 1, Integer::sum);
		}

		final Map<String, Integer> joinCountByThread = new HashMap<>();
		for (final var join : concurrency.getJoinTransitions()) {
			final String joinedThread = threadByForkId.get(List.of(join.getJoinSmtArguments().getThreadIdArguments().terms()));
			if (joinedThread != null) {
				joinCountByThread.merge(joinedThread, 1, Integer::sum);
			}
		}

		final Set<String> result = new HashSet<>();
		for (final var entry : forkCountByThread.entrySet()) {
			final String threadId = entry.getKey();
			if (entry.getValue() == 1 && joinCountByThread.getOrDefault(threadId, 0) == 1
					&& !selfForkingThreads.contains(threadId)) {
				result.add(threadId);
			}
		}
		return result;
	}

	private static Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, String> buildTrackedJoinMap(
			final IIcfg<IcfgLocation> icfg, final Set<String> trackedThreads) {
		final var concurrency = icfg.getCfgSmtToolkit().getConcurrencyInformation();
		final Map<List<Term>, String> threadByForkId = new LinkedHashMap<>();
		for (final var fork : concurrency.getThreadInstanceMap().keySet()) {
			final String threadId = fork.getNameOfForkedProcedure();
			if (trackedThreads.contains(threadId)) {
				threadByForkId.put(List.of(fork.getForkSmtArguments().getThreadIdArguments().terms()), threadId);
			}
		}
		final Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, String> result = new LinkedHashMap<>();
		for (final var join : concurrency.getJoinTransitions()) {
			final String joinedThread = threadByForkId.get(List.of(join.getJoinSmtArguments().getThreadIdArguments().terms()));
			if (joinedThread != null) {
				result.put(join, joinedThread);
			}
		}
		return result;
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

	private static void propagateMust(final Map<IcfgLocation, Set<String>> factsByLocation,
			final ArrayDeque<IcfgLocation> worklist, final IcfgLocation target, final Set<String> transferredFacts) {
		if (target == null) {
			return;
		}
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

	private static Map<String, Set<String>> computeForkReachabilityByThread(final IIcfg<IcfgLocation> icfg,
			final Set<String> threadIds) {
		final Map<String, Set<String>> directForkTargets = new HashMap<>();
		for (final var procedurePoints : icfg.getProgramPoints().entrySet()) {
			final String threadId = procedurePoints.getKey();
			for (final IcfgLocation location : procedurePoints.getValue().values()) {
				for (final IcfgEdge edge : location.getOutgoingEdges()) {
					final String forkedThread = getForkedThread(edge);
					if (forkedThread == null) {
						continue;
					}
					directForkTargets.computeIfAbsent(threadId, key -> new HashSet<>()).add(forkedThread);
				}
			}
		}

		final Set<String> candidateThreads = new HashSet<>(icfg.getProgramPoints().keySet());
		candidateThreads.addAll(directForkTargets.keySet());
		if (threadIds != null) {
			candidateThreads.retainAll(threadIds);
		}

		final Map<String, Set<String>> transitiveForkTargets = new HashMap<>();
		for (final String threadId : candidateThreads) {
			final Set<String> reachableForkTargets = new HashSet<>();
			final ArrayDeque<String> pendingForkTargets = new ArrayDeque<>(
					directForkTargets.getOrDefault(threadId, Set.of()));
			while (!pendingForkTargets.isEmpty()) {
				final String forkTarget = pendingForkTargets.removeFirst();
				if (!reachableForkTargets.add(forkTarget)) {
					continue;
				}
				for (final String nestedTarget : directForkTargets.getOrDefault(forkTarget, Set.of())) {
					pendingForkTargets.addLast(nestedTarget);
				}
			}
			if (threadIds != null) {
				reachableForkTargets.retainAll(threadIds);
			}
			transitiveForkTargets.put(threadId, Set.copyOf(reachableForkTargets));
		}
		return Map.copyOf(transitiveForkTargets);
	}

	private static Set<String> restrictToConfiguredThreads(final Set<String> threads, final Set<String> threadIds) {
		if (threadIds == null) {
			return new HashSet<>(threads);
		}
		final Set<String> restrictedThreads = new HashSet<>(threads);
		restrictedThreads.retainAll(threadIds);
		return restrictedThreads;
	}

	private static String getForkedThread(final IcfgEdge edge) {
		if (edge instanceof final IIcfgForkTransitionThreadCurrent<?> fork) {
			return fork.getNameOfForkedProcedure();
		}
		if (edge instanceof final IIcfgForkTransitionThreadOther<?> forkOther) {
			final var corresponding = forkOther.getCorrespondingIIcfgForkTransitionCurrentThread();
			return corresponding != null ? corresponding.getNameOfForkedProcedure() : null;
		}
		return null;
	}

	private static boolean isCrossThreadEdge(final IcfgEdge edge) {
		return edge instanceof IIcfgForkTransitionThreadOther<?> || edge instanceof IIcfgJoinTransitionThreadOther<?>;
	}

	/** Threads that may be active at this location */
	public Set<String> getActiveThreadsAt(final IcfgLocation location) {
		if (location == null) {
			return Set.of();
		}
		final Set<String> result = mActiveByLocation.get(location);
		return result != null ? result : Set.of();
	}

	/** Whether a thread may be active at this location */
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

	/** Threads that may have multiple concurrent instances */
	public Set<String> getMultiForkedThreads() {
		return mMultiForkedThreads;
	}
}
