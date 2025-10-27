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
	public int mMaxStatesReached = 0;
	private final int mMaxUnwindings;
	private final int mMaxInterferenceFixpointUnwindings;
	private final int mMaxParallelStates;
	private final ILogger mLogger;

	public FixpointPrintHelper(final int outUndwinding, final int innerUnwindings, final int maxstates,
			final ILogger logger) {
		mMaxUnwindings = outUndwinding;
		mMaxInterferenceFixpointUnwindings = innerUnwindings;
		mMaxParallelStates = maxstates;
		mLogger = logger;
	}

	public void printResults(final ILogger logger, final int iteration,
			final Map<String, AbsIntResult<InterferenceDomainState<STATE, ACTION, LOC>, ACTION, LOC>> resultSet,
			final Map<String, ? extends LOC> entryLocs, final StaticAbstractLocationMap<LOC> globMap, final Script script) {
		logger.error(" ");
		entryLocs.keySet().stream().forEach(l -> logger.error("Thread " + l + " " + globMap.getAbstractEntryLoc(l)));
		logger.error(" ");
		printResultCfgAnnotations(resultSet, logger, entryLocs, script);
		final String exampleThreadString = resultSet.keySet().iterator().next();
		resultSet.get(exampleThreadString).getLoc2SingleStates().get(entryLocs.values().iterator().next());
		printPrecisionLosses(iteration);
	}

	private void printPrecisionLosses(final int iteration) {
		// debug info for precision losses
		if (iteration > mMaxUnwindings) {
			mLogger.warn("Possible precision loss, widened interferences because iterations were: " + iteration
					+ " with max being: " + mMaxUnwindings);
		}
		if (mMaxStatesReached > mMaxParallelStates) {
			mLogger.warn("Used more states than max parallel allowed: " + mMaxStatesReached + " with max being: "
					+ mMaxParallelStates);
		}
	}

	public void printResultCfgAnnotations(
			final Map<String, AbsIntResult<InterferenceDomainState<STATE, ACTION, LOC>, ACTION, LOC>> resultSet,
			final ILogger logger, final Map<String, ? extends LOC> entryLocs, final Script script) {
		final Set<IcfgLocation> seenLocs = new HashSet<>();
		for (final String thread : resultSet.keySet()) {
			logger.error("\n");
			logger.error("Annotated CFG for " + thread);
			final AbsIntResult<InterferenceDomainState<STATE, ACTION, LOC>, ACTION, LOC> result = resultSet
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
			logger.error("State: " + result.getLoc2States().get(loc));
			final int parallelStateAmount = result.getLoc2States().get(loc).size();
			if (parallelStateAmount > mMaxStatesReached) {
				mMaxStatesReached = parallelStateAmount;
			}
			logger.error("Amount of parallel states: " + parallelStateAmount);
			logger.error("Unioned State: "
					+ ((InterferenceDomainState<STATE, ACTION, LOC>) result.getLoc2SingleStates().get(loc))
							.state());
			logger.error("Unioned ThreadCounter: "
					+ ((InterferenceDomainState<STATE, ACTION, LOC>) result.getLoc2SingleStates().get(loc))
							.threadCounter());
			logger.error("Unioned AbstractLocation: "
					+ ((InterferenceDomainState<STATE, ACTION, LOC>) result.getLoc2SingleStates().get(loc))
							.abstractLocationState());
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
