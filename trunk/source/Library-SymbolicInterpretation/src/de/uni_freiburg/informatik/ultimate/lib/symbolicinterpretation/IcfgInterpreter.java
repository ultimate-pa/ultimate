/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation;

import java.util.Collection;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.fluid.IFluid;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.summarizers.ICallSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.summarizers.ILoopSummarizer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.DagSizePrinter;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Interprets an interprocedural control flow graph (ICFG) starting from its initial nodes.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class IcfgInterpreter implements IEnterCallRegistrar {

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
	public IcfgInterpreter(final ILogger logger, final SymbolicTools tools,
			final IIcfg<IcfgLocation> icfg, final Collection<IcfgLocation> locationsOfInterest,
			final IDomain domain, final IFluid fluid,
			final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> loopSumFactory,
			final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> callSumFactory) {
		mLogger = logger;
		mTools = tools;
		mIcfg = icfg;
		logStartingSifa(locationsOfInterest);
		mLoiPredStorage = new MapBasedStorage(locationsOfInterest, domain, tools, logger);
		mEnterCallWorklist = new FifoWorklist<>(domain::join);
		logBuildingCallGraph();
		mCallGraph = new CallGraph(icfg, locationsOfInterest);
		logCallGraphComputed();
		mProcResCache = new ProcedureResourceCache(mCallGraph, icfg);
		enqueInitial();
		mDagInterpreter = new DagInterpreter(logger, tools, domain, fluid,
				loopSumFactory.apply(this), callSumFactory.apply(this));
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
		logStartingInterpretation();
		// TODO use topological order?
		while (mEnterCallWorklist.advance()) {
			final String procedure = mEnterCallWorklist.getWork();
			final IPredicate input = mEnterCallWorklist.getInput();
			logEnterProcedure(procedure, input);
			interpretLoisInProcedure(procedure, input);
		}
		logFinalResults();
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
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Final predicates for locations of interest are:");
			for (final Entry<IcfgLocation, IPredicate> entry : loiToPred.entrySet()) {
				mLogger.info("Location %s has predicate %s", entry.getKey(), entry.getValue());
			}
		}
	}

	private void logEnterProcedure(final String procedure, final IPredicate input) {
		mLogger.info("Interpreting procedure %s with input of size %s",
				procedure, new DagSizePrinter(input.getFormula()));
		mLogger.debug("Procedure's input is %s", input);
	}

	private void logRegisterEnterCall(final String callee, final IPredicate calleeInput) {
		mLogger.debug("Call to procedure %s received the predicate %s", callee, calleeInput);
	}

}
