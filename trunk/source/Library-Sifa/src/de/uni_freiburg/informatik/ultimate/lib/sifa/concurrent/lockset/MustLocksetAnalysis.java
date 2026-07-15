package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadActivityPreanalysis;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public final class MustLocksetAnalysis {

	private final Map<IcfgLocation, Set<String>> mMustLocksetByLocation;
	private final Set<IProgramVar> mLockVars;

	private MustLocksetAnalysis(final Map<IcfgLocation, Set<String>> mustLocksetByLocation,
			final Set<IProgramVar> lockVars) {
		mMustLocksetByLocation = mustLocksetByLocation;
		mLockVars = lockVars;
	}

	public static MustLocksetAnalysis disabled() {
		return new MustLocksetAnalysis(Map.of(), Set.of());
	}

	public static MustLocksetAnalysis create(final IIcfg<IcfgLocation> icfg, final ThreadActivityPreanalysis activity) {
		Set<IProgramVar> lockVars = LockVariableDiscovery.collectLockVars(icfg);
		if (lockVars.isEmpty()) {
			return disabled();
		}
		Map<IcfgLocation, Set<String>> mustLocksets = computeMustLocksets(icfg, lockVars);
		final Set<IProgramVar> demoted = LockVariableDiscovery.releasedWithoutHold(icfg, lockVars, mustLocksets,
				activity);
		if (!demoted.isEmpty()) {
			lockVars = new LinkedHashSet<>(lockVars);
			lockVars.removeAll(demoted);
			if (lockVars.isEmpty()) {
				return disabled();
			}
			mustLocksets = computeMustLocksets(icfg, lockVars);
		}
		return new MustLocksetAnalysis(mustLocksets, lockVars);
	}

	public Set<String> mustLocksetAt(final IcfgLocation location) {
		if (location == null) {
			return Set.of();
		}
		return mMustLocksetByLocation.getOrDefault(location, Set.of());
	}

	public Set<IProgramVar> getLockVars() {
		return mLockVars;
	}

	private static Map<IcfgLocation, Set<String>> computeMustLocksets(final IIcfg<IcfgLocation> icfg,
			final Set<IProgramVar> lockVars) {
		final Map<IcfgLocation, Set<String>> mustHeldAt = new LinkedHashMap<>();
		final Deque<IcfgLocation> worklist = new ArrayDeque<>();
		for (final IcfgLocation entry : icfg.getProcedureEntryNodes().values()) {
			mustHeldAt.put(entry, Set.of());
			worklist.add(entry);
		}
		while (!worklist.isEmpty()) {
			final IcfgLocation loc = worklist.poll();
			final Set<String> current = mustHeldAt.get(loc);
			for (final IcfgEdge edge : loc.getOutgoingEdges()) {
				final IcfgLocation target = edge.getTarget();
				if (target == null) {
					continue;
				}
				final Set<String> afterEdge = mustLocksetAfter(current, edge, lockVars);
				final Set<String> existing = mustHeldAt.get(target);
				final Set<String> merged = existing == null ? afterEdge
						: DataStructureUtils.intersection(existing, afterEdge);
				if (!merged.equals(existing)) {
					mustHeldAt.put(target, merged);
					worklist.add(target);
				}
			}
		}
		return Map.copyOf(mustHeldAt);
	}

	private static Set<String> mustLocksetAfter(final Set<String> incoming, final IcfgEdge edge,
			final Set<IProgramVar> lockVars) {
		final TransFormula tf = edge.getTransformula();
		if (tf == null) {
			return incoming;
		}
		final Set<String> result = new LinkedHashSet<>(incoming);
		for (final IProgramVar lockVar : lockVars) {
			final Rational assigned = LockEdgeClassifier.literalAssignedToOutVar(tf, lockVar);
			if (Rational.ONE.equals(assigned)) {
				result.add(lockVar.getGloballyUniqueId());
			} else if (Rational.ZERO.equals(assigned)) {
				result.remove(lockVar.getGloballyUniqueId());
			}
		}
		return Set.copyOf(result);
	}
}
