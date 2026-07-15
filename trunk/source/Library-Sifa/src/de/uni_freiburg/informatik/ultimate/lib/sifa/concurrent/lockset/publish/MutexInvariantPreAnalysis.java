package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.publish;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.LockEdgeClassifier;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.MustLocksetAnalysis;

final class MutexInvariantPreAnalysis {

	private MutexInvariantPreAnalysis() {
	}

	static Map<IProgramVar, MutexInvariant> discover(final IIcfg<IcfgLocation> icfg,
			final MustLocksetAnalysis locksetInfo, final Set<IProgramVar> lockVars,
			final Predicate<IcfgLocation> isSequential) {
		final Map<IProgramVar, Set<IProgramVar>> protectedGlobalsByLockVar =
				computeProtectedGlobalsByLockVar(icfg, locksetInfo, lockVars, isSequential);
		if (protectedGlobalsByLockVar.isEmpty()) {
			return Map.of();
		}
		final Map<IProgramVar, Set<IcfgEdge>> publishEdgesByLock =
				publishEdgesByLock(icfg, protectedGlobalsByLockVar, isSequential);
		final Map<IProgramVar, MutexInvariant> invariants = new LinkedHashMap<>();
		for (final IProgramVar lock : protectedGlobalsByLockVar.keySet()) {
			invariants.put(lock, new MutexInvariant(protectedGlobalsByLockVar.get(lock),
					publishEdgesByLock.getOrDefault(lock, Set.of()), null));
		}
		return Map.copyOf(invariants);
	}

	private static Map<IProgramVar, Set<IProgramVar>> computeProtectedGlobalsByLockVar(final IIcfg<IcfgLocation> icfg,
			final MustLocksetAnalysis locksetInfo, final Set<IProgramVar> lockVars,
			final Predicate<IcfgLocation> isSequential) {
		final Map<IProgramVar, Set<String>> alwaysHeldLockIdsByGlobal =
				alwaysHeldLockIdsByGlobal(icfg, locksetInfo, lockVars, isSequential);
		final Map<String, IProgramVar> lockById = lockById(lockVars);
		final Map<IProgramVar, Set<IProgramVar>> protectedGlobalsByLock = new LinkedHashMap<>();
		for (final Entry<IProgramVar, Set<String>> global : alwaysHeldLockIdsByGlobal.entrySet()) {
			for (final String lockId : global.getValue()) {
				protectedGlobalsByLock.computeIfAbsent(lockById.get(lockId), k -> new LinkedHashSet<>())
						.add(global.getKey());
			}
		}
		return protectedGlobalsByLock;
	}

	private static Map<IProgramVar, Set<String>> alwaysHeldLockIdsByGlobal(final IIcfg<IcfgLocation> icfg,
			final MustLocksetAnalysis locksetInfo, final Set<IProgramVar> lockVars,
			final Predicate<IcfgLocation> isSequential) {
		final Map<IProgramVar, Set<String>> heldLockIdsByGlobal = new LinkedHashMap<>();
		IcfgUtils.getAllLocations(icfg).forEach(source -> {
			if (isSequential.test(source)) {
				return;
			}
			final Set<String> heldHere = locksetInfo.mustLocksetAt(source);
			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				intersectHeldLocksForWrittenGlobals(edge, lockVars, heldHere, heldLockIdsByGlobal);
			}
		});
		return heldLockIdsByGlobal;
	}

	private static void intersectHeldLocksForWrittenGlobals(final IcfgEdge edge, final Set<IProgramVar> lockVars,
			final Set<String> heldHere, final Map<IProgramVar, Set<String>> heldLockIdsByGlobal) {
		final TransFormula tf = edge.getTransformula();
		if (tf == null) {
			return;
		}
		for (final IProgramVar written : InterferenceUtils.getChangedVars(tf)) {
			if (!written.isGlobal() || lockVars.contains(written)) {
				continue;
			}
			if (heldLockIdsByGlobal.containsKey(written)) {
				heldLockIdsByGlobal.get(written).retainAll(heldHere);
			} else {
				heldLockIdsByGlobal.put(written, new LinkedHashSet<>(heldHere));
			}
		}
	}

	private static Map<String, IProgramVar> lockById(final Set<IProgramVar> lockVars) {
		final Map<String, IProgramVar> lockById = new LinkedHashMap<>();
		lockVars.forEach(lock -> lockById.put(lock.getGloballyUniqueId(), lock));
		return lockById;
	}

	private static Map<IProgramVar, Set<IcfgEdge>> publishEdgesByLock(final IIcfg<IcfgLocation> icfg,
			final Map<IProgramVar, Set<IProgramVar>> protectedGlobalsByLock,
			final Predicate<IcfgLocation> isSequential) {
		final Map<IProgramVar, Set<IcfgEdge>> initEdgesByLock =
				initEdgesByLock(icfg, protectedGlobalsByLock, isSequential);
		final Map<IProgramVar, Set<IcfgEdge>> releaseEdgesByLock =
				releaseEdgesByLock(icfg, protectedGlobalsByLock, isSequential, initEdgesByLock);
		final Map<IProgramVar, Set<IcfgEdge>> publishEdgesByLock = new LinkedHashMap<>();
		for (final IProgramVar lock : protectedGlobalsByLock.keySet()) {
			final Set<IcfgEdge> edges = new LinkedHashSet<>(initEdgesByLock.getOrDefault(lock, Set.of()));
			edges.addAll(releaseEdgesByLock.getOrDefault(lock, Set.of()));
			if (!edges.isEmpty()) {
				publishEdgesByLock.put(lock, edges);
			}
		}
		return publishEdgesByLock;
	}

	private static Map<IProgramVar, Set<IcfgEdge>> initEdgesByLock(final IIcfg<IcfgLocation> icfg,
			final Map<IProgramVar, Set<IProgramVar>> protectedGlobalsByLock,
			final Predicate<IcfgLocation> isSequential) {
		final Map<IProgramVar, Set<IcfgEdge>> initEdges = new LinkedHashMap<>();
		IcfgUtils.getAllLocations(icfg).forEach(source -> {
			if (!isSequential.test(source)) {
				return;
			}
			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				addEdgeToLocksWhoseProtectedGlobalsItWrites(edge, protectedGlobalsByLock, initEdges);
			}
		});
		return initEdges;
	}

	private static void addEdgeToLocksWhoseProtectedGlobalsItWrites(final IcfgEdge edge,
			final Map<IProgramVar, Set<IProgramVar>> protectedGlobalsByLock,
			final Map<IProgramVar, Set<IcfgEdge>> initEdges) {
		if (edge.getTarget() == null || edge.getTransformula() == null) {
			return;
		}
		final Set<IProgramVar> written = InterferenceUtils.getChangedVars(edge.getTransformula());
		for (final Entry<IProgramVar, Set<IProgramVar>> lock : protectedGlobalsByLock.entrySet()) {
			if (!Collections.disjoint(written, lock.getValue())) {
				initEdges.computeIfAbsent(lock.getKey(), k -> new LinkedHashSet<>()).add(edge);
			}
		}
	}

	private static Map<IProgramVar, Set<IcfgEdge>> releaseEdgesByLock(final IIcfg<IcfgLocation> icfg,
			final Map<IProgramVar, Set<IProgramVar>> protectedGlobalsByLock,
			final Predicate<IcfgLocation> isSequential, final Map<IProgramVar, Set<IcfgEdge>> initEdgesByLock) {
		final Set<IProgramVar> protectingLocks = protectedGlobalsByLock.keySet();
		final Map<IProgramVar, Set<IcfgEdge>> releaseEdges = new LinkedHashMap<>();
		IcfgUtils.getAllLocations(icfg).forEach(source -> {
			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				final IProgramVar released = releasedLockOf(edge, protectingLocks);
				if (released != null && !isRedundantSequentialRelease(source, released, isSequential, initEdgesByLock)) {
					releaseEdges.computeIfAbsent(released, k -> new LinkedHashSet<>()).add(edge);
				}
			}
		});
		return releaseEdges;
	}

	private static IProgramVar releasedLockOf(final IcfgEdge edge, final Set<IProgramVar> protectingLocks) {
		if (edge.getTarget() == null) {
			return null;
		}
		return LockEdgeClassifier.releasedLockVarFromTf(edge.getTransformula(), protectingLocks);
	}

	private static boolean isRedundantSequentialRelease(final IcfgLocation source, final IProgramVar released,
			final Predicate<IcfgLocation> isSequential, final Map<IProgramVar, Set<IcfgEdge>> initEdgesByLock) {
		return isSequential.test(source) && !initEdgesByLock.getOrDefault(released, Set.of()).isEmpty();
	}
}
