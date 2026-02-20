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
		final Map<IcfgLocation, Set<String>> active = new HashMap<>();
		final Set<String> multiForked = new HashSet<>();
		final Set<String> forkTargetsSeen = new HashSet<>();
		final ArrayDeque<IcfgLocation> worklist = new ArrayDeque<>();

		for (final IcfgLocation initial : icfg.getInitialNodes()) {
			active.put(initial, new HashSet<>(Set.of(initial.getProcedure())));
			worklist.add(initial);
		}

		while (!worklist.isEmpty()) {
			final IcfgLocation source = worklist.removeFirst();
			final Set<String> sourceActive = active.get(source);

			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				final IcfgLocation target = edge.getTarget();
				if (target == null) {
					continue;
				}

				final String forkedThread = getForkedThread(edge);
				Set<String> transferred = sourceActive;
				if (forkedThread != null) {
					forkTargetsSeen.add(forkedThread);
					if (sourceActive.contains(forkedThread)) {
						multiForked.add(forkedThread);
					}
					transferred = new HashSet<>(sourceActive);
					transferred.add(forkedThread);
				}

				final Set<String> existing = active.get(target);
				if (existing == null) {
					active.put(target, new HashSet<>(transferred));
					worklist.add(target);
				} else if (existing.addAll(transferred)) {
					worklist.add(target);
				}
			}
		}

		// Conservative: once forked on a reachable path, a thread may run anywhere
		final Set<String> globallyMayBeActive = new HashSet<>(forkTargetsSeen);
		for (final IcfgLocation initial : icfg.getInitialNodes()) {
			globallyMayBeActive.add(initial.getProcedure());
		}
		if (threadIds != null) {
			globallyMayBeActive.retainAll(threadIds);
		}

		final Map<IcfgLocation, Set<String>> immutable = new HashMap<>();
		for (final var entry : active.entrySet()) {
			final Set<String> conservative = new HashSet<>(entry.getValue());
			conservative.addAll(globallyMayBeActive);
			immutable.put(entry.getKey(), Set.copyOf(conservative));
		}
		for (final var procEntry : icfg.getProgramPoints().values()) {
			for (final IcfgLocation loc : procEntry.values()) {
				immutable.computeIfAbsent(loc, key -> Set.copyOf(globallyMayBeActive));
			}
		}
		return new ThreadActivityPreanalysis(Map.copyOf(immutable), Set.copyOf(multiForked));
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
		final Set<String> result = mActiveByLocation.get(location);
		return result != null ? result : Set.of();
	}

	/** Whether a thread may be active at this location */
	public boolean mayBeActiveAt(final IcfgLocation location, final String threadId) {
		final Set<String> result = mActiveByLocation.get(location);
		return result == null || result.contains(threadId);
	}

	/** Threads that may have multiple concurrent instances */
	public Set<String> getMultiForkedThreads() {
		return mMultiForkedThreads;
	}
}
