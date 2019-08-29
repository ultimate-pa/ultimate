/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.lib.sifa;

import java.util.Collection;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.DagSizePrinter;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.IFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ICallSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ILoopSummarizer;

/**
 * Interprets an interprocedural control flow graph (ICFG) starting from its initial nodes.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class IcfgInterpreter implements IEnterCallRegistrar {

	private final SifaStats mStats;

	private final ILogger mLogger;
	private final IIcfg<IcfgLocation> mIcfg;
	private final CallGraph mCallGraph;
	private final IWorklistWithInputs<String, IPredicate> mEnterCallWorklist;
	private final MapBasedStorage mLoiPredStorage;
	private final SymbolicTools mTools;
	private final ProcedureResourceCache mProcResCache;
	private final DagInterpreter mDagInterpreter;

	/**
	 * Creates a new interpret using a custom set of locations of interest.
	 *
	 * @param locationsOfInterest Locations for which predicates shall be computed.
	 *                            You probably want to use {@link #allErrorLocations(IIcfg)}}.
	 *
	 * @see #interpret()
	 */
	public IcfgInterpreter(
			final ILogger logger,
			final IProgressAwareTimer timer,
			final SifaStats stats,
			final SymbolicTools tools,
			final IIcfg<IcfgLocation> icfg,
			final Collection<IcfgLocation> locationsOfInterest,
			final IDomain domain,
			final IFluid fluid,
			final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> loopSumFactory,
			final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> callSumFactory) {
		mStats = stats;
		mStats.start(SifaStats.Key.OVERALL_TIME);
		mLogger = logger;
		mTools = tools;
		mIcfg = icfg;
		logStartingSifa(locationsOfInterest);
		logBuildingCallGraph();
		mCallGraph = new CallGraph(icfg, locationsOfInterest);
		logCallGraphComputed();
		mLoiPredStorage = new MapBasedStorage(locationsOfInterest, domain, tools, logger);
		mEnterCallWorklist = new PriorityWorklist<>(mCallGraph.relevantProceduresTopsorted(), domain::join);
		mProcResCache = new ProcedureResourceCache(stats, mCallGraph, icfg);
		enqueInitial();
		mDagInterpreter = new DagInterpreter(logger, stats, timer, tools, domain, fluid,
				loopSumFactory.apply(this), callSumFactory.apply(this));
		mStats.stop(SifaStats.Key.OVERALL_TIME);
	}

	public static Collection<IcfgLocation> allErrorLocations(final IIcfg<IcfgLocation> icfg) {
		return icfg.getProcedureErrorNodes().values().stream().flatMap(Set::stream).collect(Collectors.toList());
	}

	private void enqueInitial() {
		final IPredicate top = mTools.top();
		mCallGraph.initialProceduresOfInterest().stream()
				.forEach(proc -> mEnterCallWorklist.add(proc, top));
	}

	/**
	 * Interprets the ICFG starting at the initial nodes.
	 *
	 * @return Map from all locations of interest given in
	 *         {@link #SymbolicInterpreter(IUltimateServiceProvider, IIcfg, Collection)} to predicates
	 *         over-approximating the program states at these locations
	 */
	public Map<IcfgLocation, IPredicate> interpret() {
		mStats.start(SifaStats.Key.OVERALL_TIME);
		logStartingInterpretation();
		while (mEnterCallWorklist.advance()) {
			final String procedure = mEnterCallWorklist.getWork();
			final IPredicate input = mEnterCallWorklist.getInput();
			logEnterProcedure(procedure, input);
			mStats.increment(SifaStats.Key.ICFG_INTERPRETER_ENTERED_PROCEDURES);
			interpretLoisInProcedure(procedure, input);
		}
		logFinalResults();
		mStats.stop(SifaStats.Key.OVERALL_TIME);
		return mLoiPredStorage.getMap();
	}

	private void interpretLoisInProcedure(final String procedure, final IPredicate initialInput) {
		mLoiPredStorage.storePredicateIfLoi(mIcfg.getProcedureEntryNodes().get(procedure), initialInput);
		final ProcedureResources resources = mProcResCache.resourcesOf(procedure);
		mDagInterpreter.interpret(
				resources.getRegexDag(), resources.getDagOverlayPathToLoisAndEnterCalls(), initialInput,
				mLoiPredStorage, this);
	}

	@Override
	public void registerEnterCall(final String callee, final IPredicate calleeInput) {
		logRegisterEnterCall(callee, calleeInput);
		mEnterCallWorklist.add(callee, calleeInput);
		// input is stored as a LOI predicate once we actually enter the call
	}

	public CallGraph callGraph() {
		return mCallGraph;
	}

	public ProcedureResourceCache procedureResourceCache() {
		return mProcResCache;
	}

	// log messages -------------------------------------------------------------------------------

	private void logStartingSifa(final Collection<IcfgLocation> locationsOfInterest) {
		mLogger.info("Started Sifa with %d locations of interest", locationsOfInterest.size());
		if (locationsOfInterest.isEmpty()) {
			mLogger.warn("No location of interest given. Interpreter runs nevertheless. You may want to cancel.");
		}
	}

	private void logBuildingCallGraph() {
		mLogger.info("Building call graph");
	}

	private void logCallGraphComputed() {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Initial procedures are %s", mCallGraph.initialProceduresOfInterest());
		}
	}

	private void logStartingInterpretation() {
		mLogger.info("Starting interpretation");
	}

	private void logFinalResults() {
		mLogger.info("Interpretation finished");
		final Map<IcfgLocation, IPredicate> loiToPred = mLoiPredStorage.getMap();
		if (loiToPred.isEmpty()) {
			mLogger.warn("No locations of interest were given");
			return;
		}
		// Change this logging. Sifa PlugIn's observer already logs non-false predicates
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Final predicates for locations of interest are:");
			for (final Entry<IcfgLocation, IPredicate> entry : loiToPred.entrySet()) {
				mLogger.info("Reachable states at location %s satisfy %s", entry.getKey(), entry.getValue());
			}
		}
	}

	private void logEnterProcedure(final String procedure, final IPredicate input) {
		mLogger.info("Interpreting procedure %s with input of size %s for LOIs",
				procedure, new DagSizePrinter(input.getFormula()));
		mLogger.debug("Procedure's input is %s", input);
	}

	private void logRegisterEnterCall(final String callee, final IPredicate calleeInput) {
		mLogger.debug("Call to procedure %s received the input %s", callee, calleeInput);
	}

}
