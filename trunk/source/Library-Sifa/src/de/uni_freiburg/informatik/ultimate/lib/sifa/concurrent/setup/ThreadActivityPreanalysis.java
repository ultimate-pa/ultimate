package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup;

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

public final class ThreadActivityPreanalysis {

	private final Map<IcfgLocation, Set<String>> mActiveByLocation;
	private final Set<String> mMultiForkedThreads;

	private ThreadActivityPreanalysis(final Map<IcfgLocation, Set<String>> activeByLocation,
			final Set<String> multiForkedThreads) {
		mActiveByLocation = activeByLocation;
		mMultiForkedThreads = multiForkedThreads;
	}

	public static ThreadActivityPreanalysis compute(final IIcfg<IcfgLocation> icfg, final Set<String> threadIds) {
		final Map<IcfgLocation, Set<String>> activeThreadsByLocation = new HashMap<>();
		final Set<String> selfForkingThreads = new HashSet<>();
		final ArrayDeque<IcfgLocation> pendingLocations = new ArrayDeque<>();

		for (final IcfgLocation initial : icfg.getInitialNodes()) {
			activeThreadsByLocation.put(initial, new HashSet<>(Set.of(initial.getProcedure())));
			pendingLocations.add(initial);
		}
		// TODO: join transitions are ignored for now
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
		return new ThreadActivityPreanalysis(Map.copyOf(finalizedActiveThreads), Set.copyOf(selfForkingThreads));
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

	/** Threads that may have multiple concurrent instances */
	public Set<String> getMultiForkedThreads() {
		return mMultiForkedThreads;
	}
}
