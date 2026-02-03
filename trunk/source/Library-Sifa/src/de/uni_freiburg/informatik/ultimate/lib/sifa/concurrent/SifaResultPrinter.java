package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.DefaultInterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public final class SifaResultPrinter {

	private final ILogger mLogger;

	public SifaResultPrinter(final ILogger logger) {
		mLogger = logger;
	}

	public void printResults(final Map<IcfgLocation, IPredicate> results, final IIcfg<IcfgLocation> icfg) {
		if (results.isEmpty()) {
			mLogger.info("=== SIFA Results: No locations analyzed ===");
			return;
		}

		mLogger.info("=== SIFA Analysis Results ===");
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

			mLogger.info("procedure %s() {", proc);
			for (final IcfgLocation loc : procLocations) {
				printAnnotatedLocation(loc, results.get(loc));
			}
			mLogger.info("}");
			mLogger.info("");
		}

		mLogger.info("=== End of SIFA Results ===");
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

			if (results.containsKey(current)) {
				ordered.add(current);
			}

			for (final IcfgEdge edge : current.getOutgoingEdges()) {
				final IcfgLocation target = edge.getTarget();
				if (target.getProcedure().equals(procedure) && visited.add(target)) {
					worklist.add(target);
				}
			}
		}

		return ordered;
	}

	private void printAnnotatedLocation(final IcfgLocation location, final IPredicate predicate) {
		mLogger.info("  // State: %s", formatPredicate(predicate));
		for (final IcfgEdge edge : location.getOutgoingEdges()) {
			final String code = formatSourceCode(edge);
			if (!code.equals("[skip]") && !code.equals("[<null>]")) {
				mLogger.info("  %s", code.substring(1, code.length() - 1)); // remove [ ]
			}
		}
	}

	public void logInterferences(final IInterferenceAbstraction interferences) {
		if (interferences.isEmpty()) {
			mLogger.debug("No interferences collected");
			return;
		}

		if (interferences instanceof DefaultInterferenceAbstraction) {
			final DefaultInterferenceAbstraction def = (DefaultInterferenceAbstraction) interferences;
			for (final String threadId : def.getThreadIds()) {
				mLogger.debug("Thread %s: %d interferences", threadId, def.getInterferenceCount(threadId));
			}
		}
	}

	private String formatSourceCode(final IcfgEdge edge) {
		if (edge instanceof CodeBlock) {
			final String code = ((CodeBlock) edge).getPrettyPrintedStatements();
			if (code != null && !code.isEmpty()) {
				return "[" + code.trim().replace("\n", "; ") + "]";
			}
		}
		return "[" + formatTransformula(edge.getTransformula()) + "]";
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
		return predicate.getFormula().toStringDirect();
	}
}
