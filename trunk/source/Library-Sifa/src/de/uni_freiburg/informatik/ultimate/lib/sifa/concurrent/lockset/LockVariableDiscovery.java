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
