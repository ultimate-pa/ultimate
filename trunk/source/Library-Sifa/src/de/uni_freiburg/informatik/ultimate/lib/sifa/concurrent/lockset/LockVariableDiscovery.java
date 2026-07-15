package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadActivityPreanalysis;

public final class LockVariableDiscovery {

	private LockVariableDiscovery() {
	}

	public static Set<IProgramVar> collectLockVars(final IIcfg<IcfgLocation> icfg) {
		final Set<IProgramVar> lockVars = new LinkedHashSet<>();
		for (final Entry<IProgramVar, List<TransFormula>> entry : writingTfsByGlobal(icfg).entrySet()) {
			if (isLockVariable(entry.getKey(), entry.getValue())) {
				lockVars.add(entry.getKey());
			}
		}
		return lockVars;
	}

	// global var -> every TransFormula that writes it
	private static Map<IProgramVar, List<TransFormula>> writingTfsByGlobal(final IIcfg<IcfgLocation> icfg) {
		final Map<IProgramVar, List<TransFormula>> writingTfsByGlobal = new LinkedHashMap<>();
		IcfgUtils.getAllLocations(icfg).forEach(source -> {
			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				final TransFormula tf = edge.getTransformula();
				if (tf == null) {
					continue;
				}
				for (final IProgramVar var : InterferenceUtils.getChangedVars(tf)) {
					if (var.isGlobal()) {
						writingTfsByGlobal.computeIfAbsent(var, k -> new ArrayList<>()).add(tf);
					}
				}
			}
		});
		return writingTfsByGlobal;
	}

	public static Set<IProgramVar> releasedWithoutHold(final IIcfg<IcfgLocation> icfg, final Set<IProgramVar> lockVars,
			final Map<IcfgLocation, Set<String>> mustLocksets, final ThreadActivityPreanalysis activity) {
		final Set<IProgramVar> demoted = new LinkedHashSet<>();
		IcfgUtils.getAllLocations(icfg).forEach(source -> {
			if (noOtherThreadsRunning(source, activity)) {
				return;
			}
			final Set<String> held = mustLocksets.getOrDefault(source, Set.of());
			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				for (final IProgramVar lockVar : lockVars) {
					if (LockEdgeClassifier.isRelease(edge.getTransformula(), lockVar)
							&& !held.contains(lockVar.getGloballyUniqueId())) {
						demoted.add(lockVar);
					}
				}
			}
		});
		return demoted;
	}

	private static boolean isLockVariable(final IProgramVar var, final List<TransFormula> writes) {
		boolean hasAcquire = false;
		for (final TransFormula tf : writes) {
			final boolean acquire = LockEdgeClassifier.isAcquire(tf, var);
			final boolean release = LockEdgeClassifier.isRelease(tf, var);
			if (!acquire && !release) {
				return false;
			}
			hasAcquire |= acquire;
		}
		return hasAcquire;
	}

	private static boolean noOtherThreadsRunning(final IcfgLocation location,
			final ThreadActivityPreanalysis activity) {
		if (activity == null) {
			return false;
		}
		final String owner = location.getProcedure();
		if (activity.getMultiForkedThreads().contains(owner)) {
			return false;
		}
		return activity.getActiveThreadsAt(location).stream().allMatch(owner::equals);
	}
}
