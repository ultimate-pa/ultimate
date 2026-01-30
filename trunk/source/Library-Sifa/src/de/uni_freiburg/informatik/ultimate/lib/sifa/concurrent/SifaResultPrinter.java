package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.DefaultInterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public final class SifaResultPrinter {

	private final ILogger mLogger;
	private final FormulaUnLet mUnletter;

	public SifaResultPrinter(final ILogger logger) {
		mLogger = logger;
		mUnletter = new FormulaUnLet();
	}

	public void printResults(final Map<IcfgLocation, IPredicate> results) {
		if (results.isEmpty()) {
			mLogger.info("=== SIFA Results: No locations analyzed ===");
			return;
		}

		final Map<String, List<Map.Entry<IcfgLocation, IPredicate>>> grouped = groupByProcedure(results);

		mLogger.info("=== SIFA Analysis Results ===");
		mLogger.info("Total locations: %d", results.size());
		mLogger.info("");

		final List<String> procedures = new ArrayList<>(grouped.keySet());
		procedures.sort(String::compareTo);

		for (final String proc : procedures) {
			final List<Map.Entry<IcfgLocation, IPredicate>> entries = grouped.get(proc);
			entries.sort(Comparator.comparing(e -> sortKey(e.getKey())));

			mLogger.info("--- Procedure/Thread: %s (%d locations) ---", proc, entries.size());
			for (final Map.Entry<IcfgLocation, IPredicate> e : entries) {
				printLocation(e.getKey(), e.getValue());
			}
			mLogger.info("");
		}

		mLogger.info("=== End of SIFA Results ===");
	}

	public void logInterferences(final IInterferenceAbstraction interferences) {
		if (interferences.isEmpty()) {
			mLogger.debug("No interferences collected");
			return;
		}

		if (interferences instanceof DefaultInterferenceAbstraction) {
			final DefaultInterferenceAbstraction def = (DefaultInterferenceAbstraction) interferences;
			for (final String threadId : def.getThreadIds()) {
				final var threadInterferences = def.getInterferencesProducedBy(threadId);
				mLogger.debug("Thread %s: %d interferences", threadId, threadInterferences.size());
			}
		}
	}

	private Map<String, List<Map.Entry<IcfgLocation, IPredicate>>> groupByProcedure(
			final Map<IcfgLocation, IPredicate> results) {

		final Map<String, List<Map.Entry<IcfgLocation, IPredicate>>> grouped = new HashMap<>();
		for (final Map.Entry<IcfgLocation, IPredicate> entry : results.entrySet()) {
			final String proc = entry.getKey().getProcedure();
			grouped.computeIfAbsent(proc, k -> new ArrayList<>()).add(entry);
		}
		return grouped;
	}

	private void printLocation(final IcfgLocation location, final IPredicate predicate) {
		mLogger.info("  %s: %s", formatLocation(location), formatPredicate(predicate));
		for (final IcfgEdge edge : location.getOutgoingEdges()) {
			mLogger.info("    -> %s [Action: %s]", formatLocation(edge.getTarget()),
					formatTransformula(edge.getTransformula()));
		}
	}

	private String formatTransformula(final UnmodifiableTransFormula transformula) {
		if (transformula == null) {
			return "<null>";
		}
		final Term unletted = mUnletter.unlet(transformula.getFormula());
		if (unletted.toString().equals("true")) {
			return "skip";
		}
		return unletted.toString();
	}

	private String sortKey(final IcfgLocation location) {
		return String.valueOf(location.getDebugIdentifier());
	}

	private String formatLocation(final IcfgLocation location) {
		return String.valueOf(location.getDebugIdentifier());
	}

	private String formatPredicate(final IPredicate predicate) {
		if (predicate == null) {
			return "<null>";
		}

		final Term unletted = mUnletter.unlet(predicate.getFormula());
		return unletted.toString();
	}
}
