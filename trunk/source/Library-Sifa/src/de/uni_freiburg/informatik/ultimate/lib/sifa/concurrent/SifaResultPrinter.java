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
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadActivityPreanalysis;

public final class SifaResultPrinter {

	public static final String BUILD_TAG = "thread-modular";

	private final ILogger mLogger;
	private final Map<IcfgLocation, Integer> mAbstractLocationIds;
	private final ThreadActivityPreanalysis mActivityPreanalysis;

	public SifaResultPrinter(final ILogger logger, final Map<IcfgLocation, Integer> abstractLocationIds,
			final ThreadActivityPreanalysis activityPreanalysis) {
		mLogger = logger;
		mAbstractLocationIds = Map.copyOf(abstractLocationIds);
		mActivityPreanalysis = activityPreanalysis;
	}

	public void printResults(final Map<IcfgLocation, IPredicate> results, final IIcfg<IcfgLocation> icfg) {
		if (results.isEmpty()) {
			mLogger.info("=== SIFA Results: No locations analyzed ===");
			return;
		}

		mLogger.info("=== SIFA Analysis Results [%s] ===", BUILD_TAG);
		mLogger.info("");

		final List<String> procedures = new ArrayList<>(icfg.getProcedureEntryNodes().keySet());
		procedures.sort(String::compareTo);

		for (final String proc : procedures) {
			final IcfgLocation entry = icfg.getProcedureEntryNodes().get(proc);
			if (entry == null) {
				continue;
			}

			final List<IcfgLocation> procLocations = getLocationsInProcedure(entry, proc, results);
			if (procLocations.isEmpty()) {
				continue;
			}

			printThreadHeader(proc);
			for (final IcfgLocation loc : procLocations) {
				printAnnotatedLocation(loc, proc, results.get(loc));
			}
			mLogger.info("}");
			mLogger.info("");
		}

		mLogger.info("=== End of SIFA Results ===");
	}

	private void printThreadHeader(final String proc) {
		final boolean selfInterference = mActivityPreanalysis.getMultiForkedThreads().contains(proc);
		if (selfInterference) {
			mLogger.info("procedure %s() { // multi-forked, applies self-interference", proc);
		} else {
			mLogger.info("procedure %s() {", proc);
		}
	}

	private List<IcfgLocation> getLocationsInProcedure(final IcfgLocation entry, final String procedure,
			final Map<IcfgLocation, IPredicate> results) {
		final List<IcfgLocation> ordered = new ArrayList<>();
		final Set<IcfgLocation> visited = new HashSet<>();
		final Deque<IcfgLocation> worklist = new ArrayDeque<>();

		worklist.add(entry);
		visited.add(entry);

		while (!worklist.isEmpty()) {
			final IcfgLocation current = worklist.removeFirst();
			ordered.add(current);

			for (final IcfgEdge edge : current.getOutgoingEdges()) {
				final IcfgLocation target = edge.getTarget();
				if (target != null && target.getProcedure().equals(procedure) && visited.add(target)) {
					worklist.add(target);
				}
			}
		}

		return ordered;
	}

	private void printAnnotatedLocation(final IcfgLocation location, final String ownerThread,
			final IPredicate predicate) {
		printAbstractLocation(location);
		printActiveThreads(location, ownerThread);
		if (predicate != null) {
			mLogger.info("  // State: %s", formatPredicate(predicate));
		} else {
			mLogger.info("  // State: <not tracked>");
		}
		for (final IcfgEdge edge : location.getOutgoingEdges()) {
			final String code = formatSourceCode(edge);
			if (!code.equals("skip") && !code.equals("<null>")) {
				mLogger.info("  %s", code);
			}
		}
	}

	private void printActiveThreads(final IcfgLocation location, final String ownerThread) {
		final Set<String> active = mActivityPreanalysis.getActiveThreadsAt(location);
		final Set<String> others = new TreeSet<>();
		for (final String threadId : active) {
			if (!threadId.equals(ownerThread)) {
				others.add(threadId);
			}
		}
		if (others.isEmpty()) {
			mLogger.info("  // active: (none)");
		} else {
			mLogger.info("  // active: %s", String.join(", ", others));
		}
	}

	private void printAbstractLocation(final IcfgLocation location) {
		final Integer absLoc = mAbstractLocationIds.get(location);
		if (absLoc != null) {
			mLogger.info("  // %s abs-loc: [%d, %d]", location.getProcedure(), absLoc, absLoc);
		}
	}

	private String formatSourceCode(final IcfgEdge edge) {
		return formatTransformula(edge.getTransformula());
	}

	private String formatTransformula(final UnmodifiableTransFormula transformula) {
		if (transformula == null) {
			return "<null>";
		}
		final String formula = transformula.getFormula().toStringDirect();
		if (formula.equals("true")) {
			return "skip";
		}
		return formula;
	}

	private String formatPredicate(final IPredicate predicate) {
		if (predicate == null) {
			return "<null>";
		}
		final String s = predicate.getFormula().toStringDirect();
		return s.replace("v_loc_", "loc_");
	}
}
