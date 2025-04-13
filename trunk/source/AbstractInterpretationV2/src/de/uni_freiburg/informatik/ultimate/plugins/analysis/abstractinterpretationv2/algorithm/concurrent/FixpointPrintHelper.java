package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.AbsIntResult;

public class FixpointPrintHelper<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {
	public FixpointPrintHelper() {
	}

	public void printCfgResults(final ILogger logger,
			final AbstractInterferenceState<STATE, ACTION, LOC> newInterferenceState,
			final AbstractInterferenceState<STATE, ACTION, LOC> newInterferenceState2, final int iteration,
			final Map<String, AbsIntResult<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>, ACTION, LOC>> resultSet,
			final Map<String, ? extends LOC> entryLocs, final AbstractLocationMap<LOC> globMap, final Script script) {
		// logger.error("\n");
		// logger.error("Fixpoint after " + iteration + " iterations found.");
		// logger.error(newInterferenceState.interferenceStrings());
		// logger.error("implies");
		// logger.error(interferenceState.interferenceStrings());
		// logger.error("\n");
		// logger.error("\n");
		logger.error(" ");
		entryLocs.keySet().stream().forEach(l -> logger.error("Thread " + l + " " + globMap.getAbstractEntryLoc(l)));
		logger.error(" ");
		printResultCfgAnnotations(resultSet, logger, entryLocs, script);
		final String exampleThreadString = resultSet.keySet().iterator().next();
		resultSet.get(exampleThreadString).getLoc2SingleStates().get(entryLocs.values().iterator().next());
		logger.error("max size reached:" + GuardedInterferenceDomainStateDisj.maxSizeReached);
	}

	public void printResultCfgAnnotations(
			final Map<String, AbsIntResult<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>, ACTION, LOC>> resultSet,
			final ILogger logger, final Map<String, ? extends LOC> entryLocs, final Script script) {
		final Set<IcfgLocation> seenLocs = new HashSet<>();
		for (final String thread : resultSet.keySet()) {
			logger.error("\n");
			logger.error("Annotated CFG for " + thread);
			final AbsIntResult<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>, ACTION, LOC> result = resultSet
					.get(thread);
			for (final LOC location : result.getLoc2Term().keySet()) {
				if (entryLocs.containsValue(location)) {
					printCfgTree(location, result, seenLocs, logger, script);
				}
			}
		}
	}

	public void printCfgTree(final IcfgLocation loc, final AbsIntResult<?, ?, ?> result,
			final Set<IcfgLocation> seenLocs, final ILogger logger, final Script script) {
		if (seenLocs.contains(loc)) {
			return;
		}
		seenLocs.add(loc);
		final var terms = result.getLoc2Term().get(loc);
		if (terms != null) {
//			logger.error("Unioned Term: " + result.getLoc2SingleStates().get(loc).getTerm(script));
			logger.error("Unioned Term: " + terms);
			logger.error("State: " + result.getLoc2SingleStates().get(loc));
//			logger.error(
//					((GuardedInterferenceDomainStateDisj<?, ?, ?>) result.getLoc2SingleStates().get(loc)).toString());
			if (loc.getOutgoingEdges().size() != 0) {
				logger.error("|");
				logger.error(loc.getOutgoingEdges());
				logger.error("|");
				logger.error("v");
			}

		}
		for (final IcfgLocation childLoc : loc.getOutgoingNodes()) {
			printCfgTree(childLoc, result, seenLocs, logger, script);
		}
	}
}
