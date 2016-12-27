/*
 * Copyright (C) 2015 Dirk Steinmetz
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.dataflow.DataflowState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.CFGInvariantsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.IInvariantPatternProcessor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.IInvariantPatternProcessorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ILinearInequalityInvariantPatternStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.LinearInequalityInvariantPatternProcessorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.LocationIndependentLinearInequalityInvariantPatternStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolantComputationStatus.ItpErrorStatus;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerUtils;

/**
 * Represents a map of invariants to a run that has been generated using a {@link IInvariantPatternProcessor} on the
 * run-projected CFG.
 *
 * @author Dirk Steinmetz, Matthias Heizmann, Betim Musa
 */
public final class PathInvariantsGenerator implements IInterpolantGenerator {

	// This is a safe and the simplest strategy: add the weakest precondition of the last two transitions of the path
	// program to
	// the predecessor of the predecessor of the error location.
	private static final boolean USE_WEAKEST_PRECONDITION = false;
	// There are two different ways to add an additional predicate to the invariant templates/patterns.
	// 1. We add the predicate to each disjunct as an additional conjunct, or
	// 2. we add the predicate as an additional disjunct.
	private static final boolean ADD_WP_TO_EACH_CONJUNCT = true;
	private static final boolean USE_LIVE_VARIABLES = false;

	private final NestedRun<? extends IAction, IPredicate> mRun;
	private final IPredicate mPrecondition;
	private final IPredicate mPostcondition;
	private final IPredicate[] mInterpolants;
	private final PredicateUnifier mPredicateUnifier;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final PredicateTransformer mPredicateTransformer;
	private final InterpolantComputationStatus mInterpolantComputationStatus;
	private IToolchainStorage mStorage;

	/**
	 * Creates a default factory.
	 *
	 * @param services
	 *            Service provider to use, for example for logging and timeouts
	 * @param storage
	 *            IToolchainstorage of the current Ultimate toolchain.
	 * @param predicateUnifier
	 *            the predicate unifier to unify final predicates with
	 * @param csToolkit
	 *            the smt manager for constructing the default {@link IInvariantPatternProcessorFactory}
	 * @param simplicationTechnique
	 * @param xnfConversionTechnique
	 * @param axioms
	 * @return a default invariant pattern processor factory
	 */
	private static IInvariantPatternProcessorFactory<?> createDefaultFactory(final IUltimateServiceProvider services,
			final IToolchainStorage storage, final PredicateUnifier predicateUnifier, final CfgSmtToolkit csToolkit,
			final boolean useNonlinerConstraints, final boolean useVarsFromUnsatCore, final boolean useLiveVars,
			final Map<IcfgLocation, Set<IProgramVar>> pathprogramLocs2LiveVars, final Settings solverSettings,
			final SimplificationTechnique simplicationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final Collection<Term> axioms) {
		final ILinearInequalityInvariantPatternStrategy strategy =
				new LocationIndependentLinearInequalityInvariantPatternStrategy(1, 1, 1, 1, 5);

		return new LinearInequalityInvariantPatternProcessorFactory(services, storage, predicateUnifier, csToolkit,
				strategy, useNonlinerConstraints, useVarsFromUnsatCore, pathprogramLocs2LiveVars, useLiveVars, solverSettings, simplicationTechnique,
				xnfConversionTechnique, axioms);
	}


	/**
	 * Generates a map of invariants to a given run, using an {@link IInvariantPatternProcessor} produced by the default
	 * {@link IInvariantPatternProcessorFactory} (with default settings).
	 *
	 * @param services
	 *            Service provider to use, for example for logging and timeouts
	 * @param storage
	 *            IToolchainstorage of the current Ultimate toolchain.
	 * @param run
	 *            an infeasible run to project into a CFG. Must only contain {@link ISLPredicate}s as states.
	 * @param precondition
	 *            the predicate to use for the first program point in the run
	 * @param postcondition
	 *            the predicate to use for the last program point in the run
	 * @param predicateUnifier
	 *            the predicate unifier to unify final predicates with
	 * @param icfg
	 * @param csToolkit
	 *            the smt manager for constructing the default {@link IInvariantPatternProcessorFactory}
	 * @param simplicationTechnique
	 * @param xnfConversionTechnique
	 */
	public PathInvariantsGenerator(final IUltimateServiceProvider services, final IToolchainStorage storage,
			final NestedRun<? extends IAction, IPredicate> run, final IPredicate precondition,
			final IPredicate postcondition, final PredicateUnifier predicateUnifier, final IIcfg<?> icfg,
			final boolean useNonlinearConstraints, final boolean useVarsFromUnsatCore, final Settings solverSettings,
			final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mRun = run;
		mStorage = storage;
		mPrecondition = precondition;
		mPostcondition = postcondition;
		mPredicateUnifier = predicateUnifier;
		mPredicateTransformer =
				new PredicateTransformer(services, icfg.getCfgSmtToolkit().getManagedScript(), simplificationTechnique, xnfConversionTechnique);

		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		Set<? extends IcfgEdge> allowedTransitions = extractTransitionsFromRun(run);
		
		final IIcfg<IcfgLocation> pathProgram = new PathProgram<>("PathInvariantsPathProgram", icfg, allowedTransitions);
		


//		Map<IcfgLocation, IPredicate> invariants = generatePathInvariants(useVarsFromUnsatCore, icfg, 
//				simplificationTechnique, xnfConversionTechnique, solverSettings, useNonlinerConstraints);
		Map<IcfgLocation, IPredicate> invariants = generateInvariantsForPathProgram(useVarsFromUnsatCore, icfg, pathProgram,
				simplificationTechnique, xnfConversionTechnique, solverSettings, useNonlinearConstraints);
		if (invariants != null) {
			// Populate resulting array
			mInterpolants = new IPredicate[mRun.getLength()];
			for (int i = 0; i < mRun.getLength(); i++) {
				BoogieIcfgLocation locFromRun = ((ISLPredicate) mRun.getStateAtPosition(i)).getProgramPoint();
				IcfgLocation locFromPathProgram = invariants.keySet().stream().filter(
						loc -> loc.toString().endsWith(locFromRun.toString())).collect(Collectors.toList()).get(0);
				mInterpolants[i] = invariants.get(locFromPathProgram);
				mLogger.info("[PathInvariants] Interpolant no " + i + " " + mInterpolants[i].toString());
			}
			mLogger.info("[PathInvariants] Invariants found and " + "processed.");
			mLogger.info("Got a Invariant map of length " + mInterpolants.length);
			mInterpolantComputationStatus = new InterpolantComputationStatus(true, null, null);
		} else {
			mInterpolants = null;
			mLogger.info("[PathInvariants] No invariants found.");
			mInterpolantComputationStatus = new InterpolantComputationStatus(false, ItpErrorStatus.ALGORITHM_FAILED, null);
		}
	}
	
	/**
	 * Compute weakest precondition for those locations which are predecessors of the error locations and successors of any loop locations. 
	 * If there are no loop locations, then we compute it only for the last two locations.
	 * @param pathProgram
	 * @return
	 */
	private Map<IcfgLocation, UnmodifiableTransFormula> computeWPForPathProgram(final IIcfg<IcfgLocation> pathProgram, ManagedScript managedScript) {
		Set<?> loopLocations = pathProgram.getLoopLocations();
		IcfgLocation errorloc = extractErrorLocationFromPathProgram(pathProgram);
		Map<IcfgLocation, IPredicate> locs2WP = new HashMap<>();
		locs2WP.put(errorloc, mPostcondition);
		List<IcfgEdge> edges2visit = errorloc.getIncomingEdges();
		int levelCounter = 0;
		while (true) {
			List<IcfgEdge> newEdges = new ArrayList<>(); 
			for (IcfgEdge e : edges2visit) {
				if (!(e instanceof IInternalAction)) {
					throw new UnsupportedOperationException("interprocedural traces are not supported (yet)");
				}
				// Compute WP for the formula of the current transition and the predicate at the target location.
				IPredicate wp = mPredicateUnifier.getOrConstructPredicate(
						mPredicateTransformer.weakestPrecondition(locs2WP.get(e.getTarget()), ((IInternalAction)e).getTransformula()));
				
				locs2WP.put(e.getSource(), wp);
				if (!loopLocations.contains(e.getSource()) || (loopLocations.isEmpty() && levelCounter < 2)) {
					newEdges.addAll(e.getSource().getIncomingEdges());
				}
			}
			levelCounter++;
			
			if (newEdges.isEmpty() || levelCounter >= 2) break;
			else {
				edges2visit = newEdges;
			}
			
		}
		return locs2WP.keySet().stream().collect(Collectors.toMap(loc -> loc, 
				loc -> TransFormulaBuilder.constructTransFormulaFromPredicate(locs2WP.get(loc), managedScript)));
	}
	
	private IcfgLocation extractErrorLocationFromPathProgram(final IIcfg<IcfgLocation> pathProgram) {
		Map<String, Set<IcfgLocation>> proc2ErrorLocations = pathProgram.getProcedureErrorNodes();
		assert (proc2ErrorLocations.keySet().size() == 1) : "Currently only one procedure with assertions is supported";
		Set<IcfgLocation> errorLocs = proc2ErrorLocations.get(proc2ErrorLocations.keySet().toArray(new String[0])[0]);
		IcfgLocation[] errorLocsAsArray = errorLocs.toArray(new IcfgLocation[errorLocs.size()]);
		assert (errorLocsAsArray.length == 1) : "There should be only one error location";
		return errorLocsAsArray[0];
	}
//
//	private final Map<BoogieIcfgLocation, IPredicate> generatePathInvariants(final boolean useVarsFromUnsatCore,
//			final IIcfg<?> icfg, final SimplificationTechnique simplificationTechnique,
//			final XnfConversionTechnique xnfConversionTechnique, final Settings solverSettings, 
//			final boolean useNonlinerConstraints) {
//		mLogger.info("Started with a run of length " + mRun.getLength());
//
//		// Project path to CFG
//		final int len = mRun.getLength();
//		// Use LinkedHashSet to iterate in insertion-order afterwards
//		final LinkedHashSet<BoogieIcfgLocation> locations = new LinkedHashSet<>(len);
//		// final Map<BoogieIcfgLocation, IcfgLocation> locationsForProgramPoint = new HashMap<>(len);
//		final LinkedHashSet<IcfgInternalAction> transitions = new LinkedHashSet<>(len - 1);
//		// final Set<CodeBlock> transitionsForAI = new LinkedHashSet<>(len - 1);
//		BoogieIcfgLocation previousLocation = null;
//		// The location where the nestedRun starts
//		final BoogieIcfgLocation startLocation = ((ISLPredicate) mRun.getStateAtPosition(0)).getProgramPoint();
//		// The location where the nestedRun ends (i.e. the error location)
//		final BoogieIcfgLocation errorLocation = ((ISLPredicate) mRun.getStateAtPosition(len - 1)).getProgramPoint();
//
//		UnmodifiableTransFormula[] weakestPreconditionOfLastTwoTransitions = null;
//		for (int i = 0; i < len; i++) {
//			final ISLPredicate pred = (ISLPredicate) mRun.getStateAtPosition(i);
//			final BoogieIcfgLocation currentLocation = pred.getProgramPoint();
//
//			// IcfgLocation location = locationsForProgramPoint.get(programPoint);
//			// if (location == null) {
//			// location = new IcfgLocation(programPoint.getDebugIdentifier(), programPoint.getProcedure(), (Payload)
//			// programPoint.getPayload());
//			// locationsForProgramPoint.put(programPoint, location);
//			// }
//
//			locations.add(currentLocation);
//
//			if (i > 0) {
//				if (!mRun.getWord().isInternalPosition(i - 1)) {
//					throw new UnsupportedOperationException("interprocedural traces are not supported (yet)");
//				}
//				// Add codeblock to transitions needed for live variable analysis
//				// transitionsForAI.add((CodeBlock) mRun.getSymbol(i-1));
//
//				final UnmodifiableTransFormula transFormula =
//						((IInternalAction) mRun.getSymbol(i - 1)).getTransformula();
//				// transitions.add(new Transition(transFormula, locations.get(i - 1), location));
//				transitions.add(new IcfgInternalAction(previousLocation, currentLocation, currentLocation.getPayload(),
//						transFormula));
//				if (USE_WP_FOR_LAST_2_TRANSITIONS && i == len - 1) {
//					final IPredicate wpFor1stTransition = mPredicateUnifier.getOrConstructPredicate(
//							mPredicateTransformer.weakestPrecondition(mPostcondition, transFormula));
//					final IPredicate wpFor2ndTransition =
//							mPredicateUnifier.getOrConstructPredicate(mPredicateTransformer.weakestPrecondition(
//									wpFor1stTransition, ((IInternalAction) mRun.getSymbol(i - 2)).getTransformula()));
//					// if (mPredicateUnifier.getTruePredicate().equals(wpFor2ndTransition)) {
//					//
//					// } else {
//					weakestPreconditionOfLastTwoTransitions = new UnmodifiableTransFormula[2];
//					weakestPreconditionOfLastTwoTransitions[0] = TransFormulaBuilder.constructTransFormulaFromPredicate(wpFor1stTransition, 
//							icfg.getCfgSmtToolkit().getManagedScript());
//					weakestPreconditionOfLastTwoTransitions[1] = TransFormulaBuilder.constructTransFormulaFromPredicate(wpFor2ndTransition, 
//							icfg.getCfgSmtToolkit().getManagedScript());
//
//					// transitions.add(new IcfgInternalAction(previousLocation, currentLocation,
//					// currentLocation.getPayload(), wpAsTransformula));
//					mLogger.info("wp computed: " + weakestPreconditionOfLastTwoTransitions);
//					// }
//				}
//			}
//			previousLocation = currentLocation;
//		}
//
//		// final ControlFlowGraph cfg =
//		// new ControlFlowGraph(locations.get(0), locations.get(len - 1), locations, transitions);
//		mLogger.info("[PathInvariants] Built projected CFG, " + locations.size() + " states and " + transitions.size()
//		+ " transitions.");
//		Map<BoogieIcfgLocation, Set<IProgramVar>> locs2LiveVariables = null;
//
//		if (USE_LIVE_VARIABLES) {
//			// // AI Module
//			Map<IcfgLocation, Set<IProgramVar>> pathprogramLocs2LiveVars  = generateLiveVariables(icfg, transitions);
//			Map<IcfgLocation, List<BoogieIcfgLocation>> pathprogramLocs2OriginalLocs = pathprogramLocs2LiveVars.keySet().stream().collect(
//					Collectors.toMap(e -> e, e -> locations.stream().filter(loc -> e.toString().endsWith(loc.toString())).collect(Collectors.toList())));
//			locs2LiveVariables = pathprogramLocs2LiveVars.entrySet().stream().collect(
//					Collectors.toMap(entry -> pathprogramLocs2OriginalLocs.get(entry.getKey()).get(0), entry -> entry.getValue()));
//			// // End AI Module
//		}
//
//		IInvariantPatternProcessorFactory<?> invPatternProcFactory = createDefaultFactory(mServices, mStorage, mPredicateUnifier, icfg.getCfgSmtToolkit(),
//				useNonlinerConstraints, useVarsFromUnsatCore, USE_LIVE_VARIABLES, locs2LiveVariables, solverSettings, simplificationTechnique,
//				xnfConversionTechnique, icfg.getCfgSmtToolkit().getAxioms());
//
//		// Generate invariants
//		final CFGInvariantsGenerator generator = new CFGInvariantsGenerator(mServices);
//		final Map<BoogieIcfgLocation, IPredicate> invariants;
//
//		// invariants = generator.generateInvariantsFromCFG(cfg, precondition, postcondition, invPatternProcFactory,
//		// useVarsFromUnsatCore, false, null);
//		final List<BoogieIcfgLocation> locationsAsList = new ArrayList<>(locations.size());
//		locationsAsList.addAll(locations);
//		final List<IcfgInternalAction> transitionsAsList = new ArrayList<>(transitions.size());
//		transitionsAsList.addAll(transitions);
//
//
//		invariants = generator.generateInvariantsForTransitions(locationsAsList, transitionsAsList, mPrecondition,
//				mPostcondition, startLocation, errorLocation, invPatternProcFactory, useVarsFromUnsatCore, false,
//				null, weakestPreconditionOfLastTwoTransitions, USE_WP_FOR_LAST_2_TRANSITIONS, ADD_WP_TO_EACH_CONJUNCT);
//
//		mLogger.info("[PathInvariants] Generated invariant map.");
//		return invariants;
//	}
//	
	
	
	private final Map<IcfgLocation, IPredicate> generateInvariantsForPathProgram(final boolean useVarsFromUnsatCore, final IIcfg<?> icfg,
			final IIcfg<IcfgLocation> pathProgram, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final Settings solverSettings, 
			final boolean useNonlinearConstraints) {
		mLogger.info("Started with a run of length " + mRun.getLength());
		
		IcfgLocation startLocation = (new ArrayList<IcfgLocation>(pathProgram.getInitialNodes())).get(0);
		IcfgLocation errorLocation = extractErrorLocationFromPathProgram(pathProgram);

		final List<IcfgLocation> locationsAsList = extractLocationsFromPathProgram(pathProgram);
		final List<IcfgInternalAction> transitionsAsList = extractTransitionsFromPathProgram(pathProgram);

		mLogger.info("[PathInvariants] Built projected CFG, " + locationsAsList.size() + " states and " + transitionsAsList.size()
		+ " transitions.");
		Map<IcfgLocation, Set<IProgramVar>> pathprogramLocs2LiveVars = null;

		if (USE_LIVE_VARIABLES) {
			pathprogramLocs2LiveVars  = computeLiveVariablesForPathProgram(pathProgram);
		}
		Map<IcfgLocation, UnmodifiableTransFormula> pathprogramLocs2WP = null;
		if (USE_WEAKEST_PRECONDITION) {
			pathprogramLocs2WP = computeWPForPathProgram(pathProgram, icfg.getCfgSmtToolkit().getManagedScript());
		}

		IInvariantPatternProcessorFactory<?> invPatternProcFactory = createDefaultFactory(mServices, mStorage, mPredicateUnifier, icfg.getCfgSmtToolkit(),
				useNonlinearConstraints, useVarsFromUnsatCore, USE_LIVE_VARIABLES, pathprogramLocs2LiveVars, solverSettings, simplificationTechnique,
				xnfConversionTechnique, icfg.getCfgSmtToolkit().getAxioms());

		// Generate invariants
		final CFGInvariantsGenerator generator = new CFGInvariantsGenerator(mServices);
		final Map<IcfgLocation, IPredicate> invariants;


		invariants = generator.generateInvariantsForTransitions(locationsAsList, transitionsAsList, mPrecondition,
				mPostcondition, startLocation, errorLocation, invPatternProcFactory, useVarsFromUnsatCore, false,
				null, pathprogramLocs2WP, USE_WEAKEST_PRECONDITION, ADD_WP_TO_EACH_CONJUNCT);

		mLogger.info("[PathInvariants] Generated invariant map.");
		return invariants;
	}

	private List<IcfgInternalAction> extractTransitionsFromPathProgram(IIcfg<IcfgLocation> pathProgram) {
		LinkedList<IcfgLocation> locs2visit = new LinkedList<>();
		locs2visit.addAll(pathProgram.getInitialNodes());
		LinkedHashSet<IcfgLocation> visitedLocs = new LinkedHashSet<>();
		LinkedList<IcfgInternalAction> edges = new LinkedList<>();
		while (!locs2visit.isEmpty()) {
			IcfgLocation loc = locs2visit.removeFirst();
			if (visitedLocs.add(loc)) {
				for (IcfgEdge e : loc.getOutgoingEdges()) {
					locs2visit.addLast(e.getTarget());
					if (!(e instanceof IInternalAction)) {
						throw new UnsupportedOperationException("interprocedural traces are not supported (yet)");
					}
					edges.addLast(new IcfgInternalAction(e.getSource(), e.getTarget(), e.getPayload(), ((IInternalAction)e).getTransformula()));
				}
			}
		}
		return edges;
	}

	private List<IcfgLocation> extractLocationsFromPathProgram(IIcfg<IcfgLocation> pathProgram) {
		LinkedList<IcfgLocation> locs2visit = new LinkedList<>();
		locs2visit.addAll(pathProgram.getInitialNodes());
		LinkedHashSet<IcfgLocation> visitedLocs = new LinkedHashSet<>();
		while (!locs2visit.isEmpty()) {
			IcfgLocation loc = locs2visit.removeFirst();
			if (visitedLocs.add(loc)) {
				for (IcfgEdge e : loc.getOutgoingEdges()) {
					locs2visit.addLast(e.getTarget());
				}
			}
		}
		
		
		return new ArrayList<IcfgLocation>(visitedLocs);
	}



	



	/**
	 * Computes for each location of the given path program a set of variables which are <emph> live </emph>.
	 * @param pathProgram
	 * @return
	 */
	private Map<IcfgLocation, Set<IProgramVar>> computeLiveVariablesForPathProgram(final IIcfg<IcfgLocation> pathProgram) {
		// allow for 20% of the remaining time
		final IProgressAwareTimer timer = mServices.getProgressMonitorService().getChildTimer(0.2);
		final IAbstractInterpretationResult<DataflowState<IcfgEdge>, IcfgEdge, IProgramVar, IcfgLocation> result =
				AbstractInterpreter.runFutureDataflowDomain(pathProgram, timer, mServices, true, mLogger);
		final Map<IcfgLocation, Set<DataflowState<IcfgEdge>>> loc2states = result.getLoc2States();
		Map<IcfgLocation, Set<IProgramVar>> locs2liveVars = new HashMap<>();
		for (Map.Entry<IcfgLocation, Set<DataflowState<IcfgEdge>>> entry : loc2states.entrySet()) {
			locs2liveVars.put(entry.getKey(), entry.getValue().stream().map(e -> e.getVariables()).collect(HashSet::new, HashSet::addAll, HashSet::addAll));
		}
		return locs2liveVars;
	}

	private Set<? extends IcfgEdge> extractTransitionsFromRun(final NestedRun<? extends IAction, IPredicate> run) {
		final int len = run.getLength();
		final LinkedHashSet<IcfgInternalAction> transitions = new LinkedHashSet<>(len - 1);
		BoogieIcfgLocation previousLocation = null;

		for (int i = 0; i < len; i++) {
			final ISLPredicate pred = (ISLPredicate) run.getStateAtPosition(i);
			final BoogieIcfgLocation currentLocation = pred.getProgramPoint();
			if (i > 0) {
				if (!run.getWord().isInternalPosition(i - 1)) {
					throw new UnsupportedOperationException("interprocedural traces are not supported (yet)");
				}
				final UnmodifiableTransFormula transFormula =
						((IInternalAction) run.getSymbol(i - 1)).getTransformula();
				transitions.add(new IcfgInternalAction(previousLocation, currentLocation, currentLocation.getPayload(),
						transFormula));
			}
			previousLocation = currentLocation;
		}
		return transitions;
	}

	@Override
	public Word<? extends IAction> getTrace() {
		return mRun.getWord();
	}

	@Override
	public IPredicate getPrecondition() {
		return mPrecondition;
	}

	@Override
	public IPredicate getPostcondition() {
		return mPostcondition;
	}

	@Override
	public Map<Integer, IPredicate> getPendingContexts() {
		throw new UnsupportedOperationException("Call/Return not supported yet");
	}

	@Override
	public PredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

	/**
	 * Returns a sequence of interpolants (see definition in {@link IInterpolantGenerator}) the trace which is
	 * mRun.getWord() with an additional property. If the ProgramPoint and position i and k coincide then the
	 * interpolants at position i and k coincide.
	 *
	 * @return sequence of interpolants according to the run provided in the constructor or null if no such sequence has
	 *         been found; without first interpolant (the precondition)
	 */
	@Override
	public IPredicate[] getInterpolants() {
		if (mInterpolants == null) {
			return null;
		}
		final IPredicate[] interpolantMapWithOutFirstInterpolant = new IPredicate[mInterpolants.length - 2];
		System.arraycopy(mInterpolants, 1, interpolantMapWithOutFirstInterpolant, 0, mInterpolants.length - 2);
		return interpolantMapWithOutFirstInterpolant;
	}

	@Override
	public boolean isPerfectSequence() {
		final BackwardCoveringInformation bci = TraceCheckerUtils.computeCoverageCapability(mServices, this, mLogger);
		final boolean isPerfect = bci.getPotentialBackwardCoverings() == bci.getSuccessfullBackwardCoverings();
		return isPerfect;
	}

	@Override
	public InterpolantComputationStatus getInterpolantComputationStatus() {
		return mInterpolantComputationStatus;
	}

}
