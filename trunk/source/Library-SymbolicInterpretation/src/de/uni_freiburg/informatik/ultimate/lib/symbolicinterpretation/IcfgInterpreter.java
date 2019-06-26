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
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.DagSizePrinter;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Interprets a whole interprocedural control flow graph (ICFG).
 * 
 * @author schaetzc@tf.uni-freiburg.de
 */
public class IcfgInterpreter {

	private final ILogger mLogger;
	private final IIcfg<IcfgLocation> mIcfg;
	private final CallGraph mCallGraph;
	private final IWorklistWithInputs<String, IPredicate> mEnterCallWorklist;
	private final Map<IcfgLocation, IPredicate> mPredicatesForLoi = new HashMap<>();
	private final SymbolicTools mTools;
	private final IDomain mDomain;
	private final InterpreterResources mInterpreterResources;
	private final ProcedureResourceCache mProcResCache;
	
	/**
	 * Creates a new interpreter assuming all error locations to be locations of interest.
	 *
	 * @see #interpret()
	 */
	public IcfgInterpreter(final ILogger logger, final SymbolicTools tools, final IIcfg<IcfgLocation> icfg,
			final IDomain domain, final InterpreterResources resources) {
		this(logger, tools, icfg, errorLocations(icfg), domain, resources);
	}

	private static Collection<IcfgLocation> errorLocations(final IIcfg<IcfgLocation> icfg) {
		return icfg.getProcedureErrorNodes().values().stream().flatMap(Set::stream).collect(Collectors.toList());
	}

	/**
	 * Creates a new interpret using a custom set of locations of interest.
	 * 
	 * @param locationsOfInterest Locations for which predicates shall be computed.
	 * 
	 * @see #interpret()
	 */
	public IcfgInterpreter(final ILogger logger, final SymbolicTools tools,
			final IIcfg<IcfgLocation> icfg, final Collection<IcfgLocation> locationsOfInterest,
			final IDomain domain, final InterpreterResources resources) {
		mLogger = logger;
		mTools = tools;
		mIcfg = icfg;
		mDomain = domain;
		mInterpreterResources = resources;
		logStartingSifa(locationsOfInterest);
		mEnterCallWorklist = new FifoWorklist<>(domain::join);
		logBuildingCallGraph();
		mCallGraph = new CallGraph(icfg, locationsOfInterest);
		logCallGraphComputed();
		mProcResCache = new ProcedureResourceCache(mCallGraph, icfg);
		initPredicates(locationsOfInterest);
		enqueInitial();
	}

	private void enqueInitial() {
		final IPredicate top = mTools.top();
		mCallGraph.initialProceduresOfInterest().stream()
				.peek(proc -> mEnterCallWorklist.add(proc, top))
				.map(mIcfg.getProcedureEntryNodes()::get)
				.forEach(procEntry -> storePredicateIfLoi(procEntry, top));
	}

	private void initPredicates(final Collection<IcfgLocation> locationsOfInterest) {
		final IPredicate bottom = mTools.bottom();
		locationsOfInterest.forEach(loi -> mPredicatesForLoi.put(loi, bottom));
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
			interpretLoisInProcedure(mProcResCache.resourcesOf(procedure), input);
		}
		logFinalResults();
		return mPredicatesForLoi;
	}

	private void interpretLoisInProcedure(final ProcedureResources resources, final IPredicate initialInput) {
		mInterpreterResources.getDagInterpreter().interpret(
				resources.getRegexDag(), resources.getDagOverlayPathToLoisAndEnterCalls(), initialInput);
	}

	public void registerEnterCall(final String callee, final IPredicate calleeInput) {
		logRegisterEnterCall(callee, calleeInput);
		mEnterCallWorklist.add(callee, calleeInput);
		storePredicateIfLoi(mIcfg.getProcedureEntryNodes().get(callee), calleeInput);
	}

	public void storePredicateIfLoi(final IcfgLocation location, final IPredicate addPred) {
		mPredicatesForLoi.computeIfPresent(location,
				(loi, oldPred) -> joinLoiPredicate(loi, oldPred, addPred));
	}

	private IPredicate joinLoiPredicate(final IcfgLocation loi, final IPredicate oldPred, final IPredicate addPred) {
		logBeforeRegisterLoi(loi, addPred);
		final IPredicate newPred = mDomain.join(oldPred, addPred);
		logAfterRegisterLoi(loi, addPred, newPred);
		return newPred;
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
		if (mPredicatesForLoi.isEmpty()) {
			mLogger.warn("No locations of interest were given");
			return;
		}
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Final predicates for locations of interest are:");
			for (final Entry<IcfgLocation, IPredicate> entry : mPredicatesForLoi.entrySet()) {
				mLogger.info("Location %s has predicate %s", entry.getKey(), entry.getValue());
			}
		}
	}

	private void logEnterProcedure(final String procedure, final IPredicate input) {
		mLogger.info("Interpreting procedure %s with input of size %s", procedure, new DagSizePrinter(input.getFormula()));
		mLogger.debug("Procedure's input is %s", input);
	}

	private void logRegisterEnterCall(final String callee, final IPredicate calleeInput) {
		mLogger.debug("Call to procedure %s received the predicate %s", callee, calleeInput);
	}

	private void logBeforeRegisterLoi(final IcfgLocation loi, final IPredicate addPred) {
		mLogger.debug("LOI %s received the predicate %s", loi, addPred);
	}

	private void logAfterRegisterLoi(final IcfgLocation loi, final IPredicate addedPred, final IPredicate newPred) {
		if (addedPred == newPred) {
			mLogger.debug("Updated predicate for LOI %s is identical", loi);
		} else {
			mLogger.debug("Updated predicate for LOI %s is %s", loi, newPred);
		}
	}

}
