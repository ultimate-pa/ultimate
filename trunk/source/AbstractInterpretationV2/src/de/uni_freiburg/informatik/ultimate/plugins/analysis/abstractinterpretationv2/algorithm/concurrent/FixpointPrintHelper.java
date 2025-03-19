package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.AbsIntResult;

public class FixpointPrintHelper<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {
	public FixpointPrintHelper() {
	}

	public void printCfgResults(final ILogger logger,
			final AbstractInterferenceState<STATE, ACTION> newInterferenceState,
			final AbstractInterferenceState<STATE, ACTION> interferenceState, final int iteration,
			final Map<String, AbsIntResult<STATE, ACTION, LOC>> resultSet, final Map<String, ? extends LOC> entryLocs) {
		// logger.error("\n");
		// logger.error("Fixpoint after " + iteration + " iterations found.");
		// logger.error(newInterferenceState.interferenceStrings());
		// logger.error("implies");
		// logger.error(interferenceState.interferenceStrings());
		// logger.error("\n");
		// logger.error("\n");
		printResultCfgAnnotations(resultSet, logger, entryLocs);
	}

	public void printResultCfgAnnotations(final Map<String, AbsIntResult<STATE, ACTION, LOC>> resultSet,
			final ILogger logger, final Map<String, ? extends LOC> entryLocs) {
		final Set<IcfgLocation> seenLocs = new HashSet<>();
		for (final String thread : resultSet.keySet()) {
			logger.error("\n");
			logger.error("Annotated CFG for " + thread);
			final AbsIntResult<STATE, ACTION, LOC> result = resultSet.get(thread);
			for (final LOC location : result.getLoc2Term().keySet()) {
				if (entryLocs.containsValue(location)) {
					printCfgTree(location, result, seenLocs, logger);
				}
			}
		}
	}

	public void printCfgTree(final IcfgLocation loc, final AbsIntResult<?, ?, ?> result,
			final Set<IcfgLocation> seenLocs, final ILogger logger) {
		if (seenLocs.contains(loc)) {
			return;
		}
		seenLocs.add(loc);
		final var terms = result.getLoc2Term().get(loc);
		if (terms != null) {
			logger.error("[STATE: " + result.getLoc2SingleStates().get(loc) + "]");
			logger.error("[THREADS: " + ((GuardedInterferenceDomainState<?, ?>) result.getLoc2SingleStates().get(loc))
					.getThreadInstanceState().toString() + "]");
			if (loc.getOutgoingEdges().size() != 0) {
				logger.error("|");
				logger.error(loc.getOutgoingEdges());
				logger.error("|");
				logger.error("v");
			}
		}
		for (final IcfgLocation childLoc : loc.getOutgoingNodes()) {
			printCfgTree(childLoc, result, seenLocs, logger);
		}
	}
}
