/*
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorlocalization;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IRelevanceInformation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.BasicInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AcyclicSubgraphMerger;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.RelevanceInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.FaultLocalizationRelevanceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.FaultLocalizationRelevanceChecker.ERelevanceStatus;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.IPredicatePostprocessor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.QuantifierEliminationPostprocessor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.TraceInterpolationException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RelevanceAnalysisMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.DefaultTransFormulas;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

/**
 * Relevance information of a trace. Used to compute the relevant statements in an Error trace that are relevant (or
 * responsible) for the reaching the error trace according to some Error Relevance criterion. Currently we have two
 * relevance criterion 1) Non-Flow Sensitive 2) Flow Sensitive.
 *
 * @author Numair Mansur
 * @author Matthias Heizmann
 * @author Christian Schilling
 */
public class FlowSensitiveFaultLocalizer<LETTER extends IIcfgTransition<?>> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final IRelevanceInformation[] mRelevanceOfTrace;
	private final IIcfgSymbolTable mSymbolTable;
	private final PredicateFactory mPredicateFactory;
	private final ErrorLocalizationStatisticsGenerator mErrorLocalizationStatisticsGenerator;
	/**
	 * Apply quantifier elimination during the computation of pre and wp. If set to true, there is a higher risk that we
	 * run into a timeout. If set to false, there is a higher risk that the SMT solver returns unknown.
	 */
	private final boolean mApplyQuantifierElimination = true;

	public FlowSensitiveFaultLocalizer(final NestedRun<LETTER, IPredicate> counterexample,
			final INestedWordAutomaton<LETTER, IPredicate> cfg, final IUltimateServiceProvider services,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final ModifiableGlobalsTable modifiableGlobalsTable, final IPredicateUnifier predicateUnifier,
			final RelevanceAnalysisMode faultLocalizationMode, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final IIcfgSymbolTable symbolTable,
			final IIcfg<IcfgLocation> IIcfg) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mSymbolTable = symbolTable;
		mPredicateFactory = predicateFactory;
		mRelevanceOfTrace = initializeRelevanceOfTrace(counterexample);
		mErrorLocalizationStatisticsGenerator = new ErrorLocalizationStatisticsGenerator();

		mErrorLocalizationStatisticsGenerator.continueErrorLocalizationTime();
		try {
			if (faultLocalizationMode == RelevanceAnalysisMode.SINGLE_TRACE) {
				doNonFlowSensitiveAnalysis(counterexample.getWord(), predicateUnifier.getTruePredicate(),
						predicateUnifier.getFalsePredicate(), modifiableGlobalsTable, csToolkit);
			}
			if (faultLocalizationMode == RelevanceAnalysisMode.MULTI_TRACE) {
				doFlowSensitiveAnalysis(counterexample, predicateUnifier.getTruePredicate(), cfg,
						modifiableGlobalsTable, csToolkit, IIcfg);
			}
		} catch (final ToolchainCanceledException tce) {
			mErrorLocalizationStatisticsGenerator.stopErrorLocalizationTime();
			final RunningTaskInfo rti = new RunningTaskInfo(getClass(),
					"doing error localization for trace of length " + counterexample.getLength());
			throw new ToolchainCanceledException(tce, rti);
		}
		mErrorLocalizationStatisticsGenerator.reportSuccesfullyFinished();
		mErrorLocalizationStatisticsGenerator.stopErrorLocalizationTime();

		final StatisticsData stat = new StatisticsData();
		stat.aggregateBenchmarkData(mErrorLocalizationStatisticsGenerator);
		final IResult benchmarkResult =
				new StatisticsResult<>(Activator.PLUGIN_NAME, "ErrorLocalizationStatistics", stat);
		services.getResultService().reportResult(Activator.PLUGIN_ID, benchmarkResult);
	}

	/**
	 * Construct RelevanceInformation array for trace.
	 *
	 * @return array with empty IRelevanceInformation for each IAction in the trace.
	 */
	private IRelevanceInformation[] initializeRelevanceOfTrace(final NestedRun<LETTER, IPredicate> counterexampleRun) {
		final IRelevanceInformation[] result = new IRelevanceInformation[counterexampleRun.getLength() - 1];
		final NestedWord<LETTER> counterexampleWord = counterexampleRun.getWord();
		for (int i = 0; i < counterexampleWord.length(); i++) {
			final IRelevanceInformation relevancyOfAction = new RelevanceInformation(
					Collections.singletonList(counterexampleWord.getSymbol(i)), false, false, false, false, false);
			result[i] = relevancyOfAction;
		}
		return result;
	}
	
	/**
	 * Construct conglomerate for the sub-graph.
	 * @return 
	 * 
	 */
	private UnmodifiableTransFormula constructConglomerate(final Integer startPosition, final Integer endPosition,
			final Set<IcfgEdge> subGraphEdges, final NestedRun<LETTER, IPredicate> counterexample, 
			final IIcfg<IcfgLocation> IIcfg) {
		
		final IcfgLocation startLocation = 
				((ISLPredicate) counterexample.getStateAtPosition(startPosition)).getProgramPoint();
		IcfgEdge startLocErrorEdge = null;
		
		final Set<IcfgLocation> endLocations = new HashSet<>();
		final IcfgLocation endLocation = 
				((ISLPredicate) counterexample.getStateAtPosition(endPosition + 1)).getProgramPoint();
		endLocations.add(endLocation);
		// Location before the start location
		final IcfgLocation preStartLocation = 	
				((ISLPredicate) counterexample.getStateAtPosition(startPosition-1)).getProgramPoint();
				
		for (final IcfgEdge edge : preStartLocation.getOutgoingEdges()) {
			final IcfgLocation succLoc = edge.getTarget();
			if(succLoc == startLocation) {
				startLocErrorEdge = edge;
			}
		}
		final AcyclicSubgraphMerger asm = new AcyclicSubgraphMerger(mServices, IIcfg, subGraphEdges, startLocation, startLocErrorEdge, endLocations);
		return asm.getTransFormula(endLocation);
	}
	
	
	/**
	 * From within the branch, compute the final
	 * branch-out location.
	 * 
	 * @param startLocation
	 * @param endLocation
	 * @param informationFromCfg
	 * @param counterexample 
	 * @return
	 */
	private Map<Integer, Set<IcfgEdge>> computeBranchOutLocation(final int startLocation, final int endLocation,
			final Map<Integer, Map<Integer, Set<IcfgEdge>>> informationFromCfg,
				final NestedRun<LETTER,IPredicate> counterexample){
		final Map<Integer, Set<IcfgEdge>> result = new HashMap<>(); 
		final Set<IcfgEdge> subgraphEdges = new HashSet<>();
		// Add the edges of the trace
		subgraphEdges.addAll(computePathEdges(counterexample, startLocation, endLocation));
		Integer branchOut = startLocation;
		for(int i=endLocation; i>= startLocation; i--) {
			final Map<Integer, Set<IcfgEdge>> branchIn = informationFromCfg.get(i);
			if(branchIn != null) {
				final ArrayList<Integer> branchOuts = new ArrayList<>(branchIn.keySet());
				// Unionize all alternative path edges.
				for(final Integer subBranchOut : branchOuts) {
					subgraphEdges.addAll(branchIn.get(subBranchOut));
				}
				branchOuts.sort(Collections.reverseOrder());
				if(branchOuts.get(0) < branchOut) {
					Map<Integer, Set<IcfgEdge>> updatedBranchOut = computeBranchOutLocation(branchOuts.get(0), i, 
							informationFromCfg, counterexample);
					for (Integer k: updatedBranchOut.keySet()) {
						branchOut = k;
						subgraphEdges.addAll(updatedBranchOut.get(k));
					}
				}
			}
		}
		result.put(branchOut, subgraphEdges);
		return result;
	}
	
	/**
	 * Post process information from CFG.
	 * @param counterexample 
	 * @param informationFromCfg 
	 * @param startLocation, start location in error trace
	 * @param endLocation, end location in the error trace
	 * @return 
	 */
	
	private Map<Integer, Map<Integer, Set<IcfgEdge>>> postProcessInformationFromCFG(NestedRun<LETTER, IPredicate> counterexample,
			final Map<Integer, Map<Integer, Set<IcfgEdge>>> informationFromCfg, final int startLocation, 
				 final int endLocation) {
		// Now we have to take the union of the edges
		final Map<Integer, Map<Integer, Set<IcfgEdge>>> result = new HashMap<>();
		for(int i = endLocation; i >= startLocation; i --) {
			// Check if i is a branch-in Location.
			final Map<Integer, Set<IcfgEdge>> branchIn = informationFromCfg.get(i);
			// If yes, get the minimum branch-out location
			Integer branchOut = null;
			Map<Integer, Set<IcfgEdge>> finalBranchOut = new HashMap<>();
			if(branchIn != null) {
				result.put(i, branchIn); // Add all the information.				
				final ArrayList<Integer> branchOuts = new ArrayList<>(branchIn.keySet());			
				Collections.sort(branchOuts);
				branchOut = branchOuts.get(0);
				finalBranchOut = computeBranchOutLocation(branchOut, i, informationFromCfg, counterexample);
				for(Integer k : finalBranchOut.keySet()) {
					if(result.get(i).get(k) != null) {
						result.get(i).get(k).addAll(finalBranchOut.get(k));
					} else {
						result.get(i).putAll(finalBranchOut);
					}
				}
			}		
		}
		return result;
	}
	
	/**
	 * Return all the edges in a path in the CFG
	 * 
	 */
	
	private Set<IcfgEdge> computePathEdges(final NestedRun<LETTER, IPredicate> trace, Integer startState, Integer endState) {
		
		final Set<IcfgEdge> pathEdges = new HashSet<>();
		for(int state = startState; state < endState; state++) {
			final IcfgLocation currentICFGloc = ((ISLPredicate) trace.getStateAtPosition(state)).getProgramPoint();
			final IcfgLocation nextICFGloc = ((ISLPredicate) trace.getStateAtPosition(state+1)).getProgramPoint();
			for (final IcfgEdge edge : currentICFGloc.getOutgoingEdges()) {
				final IcfgLocation succLoc = edge.getTarget();
				if(succLoc == nextICFGloc) {
					pathEdges.add(edge);
				}
			}
		}
		return pathEdges;
	}
	
	/**
	 * COMPUTE INFORMATION FROM CFG
	 * 
	 */
	private Map<Integer, Map<Integer, Set<IcfgEdge>>> computeInformationFromCFG(final NestedRun<LETTER, IPredicate> trace, 
			final INestedWordAutomaton<LETTER, IPredicate> cfg, final ManagedScript csToolkit) {
		// Get all the edges in the path in the trace.
		final Map<Integer, Map<Integer, Set<IcfgEdge>>> result = new HashMap<>();
		// Create a Map of Programpoints in the CFG to States of the CFG.
		final Map<IcfgLocation, IPredicate> programPointToState = new HashMap<>();
		for (final IPredicate cfgState : cfg.getStates()) {
			final ISLPredicate islState = (ISLPredicate) cfgState;
			final IcfgLocation programPoint = islState.getProgramPoint();
			programPointToState.put(programPoint, cfgState);
		}
		// Trace elements (transitions) of the given path in the CFG.
		final List<LETTER> traceElements = new ArrayList<>();
		for(int i = 0; i < trace.getLength() -1 ; i++) {
			traceElements.add(trace.getSymbol(i));
		}
		// For each state s, find out if there is an outgoing edge from 
		// s to s1, such that s1 is not in the counterexample. 
		// Check if there is a path from s1 back to the error trace. This is called
		// an alternative path. 
		//
		// Save the alternative path, and recursively find alternative paths for
		// the alternative path we just found.
		for (int posOfStartState = 0; posOfStartState < trace.getLength() - 1; posOfStartState++) {
			final Set<IcfgEdge> subgraphEdges = new HashSet<>();
			// Start state s
			final IPredicate startStateInTrace = trace.getStateAtPosition(posOfStartState);
			// ICFG Location for the state s
			final IcfgLocation programpointOfStartStateInTrace = ((ISLPredicate) startStateInTrace).getProgramPoint();
			// the startStateInCfg will be forbidden in the alternative path (FORBIDDEN STATE BUG)
			final IPredicate startStateInCfg = programPointToState.get(programpointOfStartStateInTrace);
			// Possible end points in the error trace..
			final Set<IPredicate> possibleEndPoints =
					computePossibleEndpoints(trace, programPointToState, posOfStartState);
			// Immediate succesors of s1 in the CFG.
			final Iterable<OutgoingInternalTransition<LETTER, IPredicate>> immediateSuccesors =
					cfg.internalSuccessors(startStateInCfg);
			// Iterate over all the immediate succesors of s1 in the CFG.
			for (final OutgoingInternalTransition<LETTER, IPredicate> transition : immediateSuccesors) {
				final IPredicate immediateSuccesor = transition.getSucc();
				if(traceElements.contains(transition.getLetter())) {
					// do nothing because this transition is present in 
					// the given trace.
				} else {
					// the transition is not in the given trace.
					final NestedWord<LETTER> notGuard =
							new NestedWord<>(transition.getLetter(), NestedWord.INTERNAL_POSITION);
					NestedRun<LETTER, IPredicate> alternativePath = new NestedRun<>(notGuard,
							new ArrayList<>(Arrays.asList(startStateInCfg, transition.getSucc())));
					final NestedRun<LETTER, IPredicate> remainingPath =
							findPathInCfg(immediateSuccesor, startStateInCfg, possibleEndPoints, cfg);
					if (remainingPath != null) {
						// An alternative path exists (here called the remaining path) from the successor
						// state of the start state back to the given trace.
						alternativePath = alternativePath.concatenate(remainingPath);
						// Add all the edges of the alternative path
						subgraphEdges.addAll(computePathEdges(alternativePath, 0, alternativePath.getLength() -1));
						Map<Integer, Map<Integer, Set<IcfgEdge>>> subResult = 
								computeInformationFromCFG(alternativePath, cfg, csToolkit);
						// Add all the edges of the alternative paths
						for(final Integer key : subResult.keySet()) {
							for(final Integer subKey : subResult.get(key).keySet()) {
								subgraphEdges.addAll(subResult.get(key).get(subKey));
							}
						}
						// The state in the given trace where the alternative path ends
						final IPredicate lastStateOfAlternativePath =
								alternativePath.getStateAtPosition(alternativePath.getLength() - 1);		
						final List<Integer> endPosition = computeEndpointOfAlternativePath(trace,
								posOfStartState, lastStateOfAlternativePath);
						for (final Integer i : endPosition) {
							// If the Branch-In Location is not in the map, then add it.
							subgraphEdges.addAll(computePathEdges(trace, posOfStartState, i));
							if (result.get(i - 1) == null) {
								// add to the result
								final Map<Integer, Set<IcfgEdge>> branchInPosMap = new HashMap<>();
								// Since in the alternative path, we do not include the first element,
								// hence we have to add 1 on all locations.							
									branchInPosMap.put(posOfStartState, subgraphEdges);
									result.put(i - 1, branchInPosMap);
							} else {
								// It is in the map,
								// add to result
								// Since in the alternative path, we do not include the first element,
								// hence we have to add 1 on all locations.
									result.get(i - 1).put(posOfStartState, subgraphEdges);
							}
						}
					}
				}
			}
		}
		return result;
	}

	/**
	 * Returns a List of locations for the occurrence of a state in the Error Trace. There can be multiple locations, in
	 * case of a loop unrolling. Computing the end point (position of the IN-BRANCH) an alternative path. Search for the
	 * last state in the trace that satisfies the following properties. - position in trace is larger than
	 * posOfStartState - program point of the state coincides with - program point of lastStateOfAlternativePath Also
	 * takes care of the case when for a state in CFG, there are more then one Occurrences of the corresponding state in
	 * the error trace. This can happen, for example, in the case of a loop un-rolling.
	 */
	private List<Integer> computeEndpointOfAlternativePath(final NestedRun<LETTER, IPredicate> counterexample,
			final int posOfStartState, final IPredicate lastStateOfAlternativePath) {
		final List<Integer> endPoints = new ArrayList<>();
		for (int j = counterexample.getLength() - 1; j > posOfStartState; j--) {
			final IPredicate stateAtPosJ = counterexample.getStateAtPosition(j);
			final IcfgLocation programpointAtPosJ = ((ISLPredicate) stateAtPosJ).getProgramPoint();
			final IcfgLocation programpointOfLastState = ((ISLPredicate) lastStateOfAlternativePath).getProgramPoint();
			if (programpointOfLastState.equals(programpointAtPosJ)) {
				// position of state in the counter example where the branch ends
				endPoints.add(j);
				// return j;
			}
		}
		if (!endPoints.isEmpty()) {
			return endPoints;
		}
		throw new AssertionError("endpoint not in trace");
	}

	/**
	 * End points are the cfg states (resp. program points) of all successive states (successors of currentPosition) in
	 * the trace excluding the last state (which corresponds to the error location).
	 *
	 * @param programPointStateMap
	 *            map from program points to states in cfg
	 */
	private Set<IPredicate> computePossibleEndpoints(final NestedRun<LETTER, IPredicate> counterexample,
			final Map<IcfgLocation, IPredicate> programPointStateMap, final int currentPosition) {
		final Set<IPredicate> possibleEndPoints = new HashSet<>();
		for (int j = currentPosition + 1; j < counterexample.getStateSequence().size() - 1; j++) {
			// runs only up to size-1 because we do not include the last state (2 Assertion Bug)
			possibleEndPoints.add(
					programPointStateMap.get(((ISLPredicate) counterexample.getStateAtPosition(j)).getProgramPoint()));
		}
		return possibleEndPoints;
	}

	/**
	 * Computes relevance criterion variables (Unsatisfiable core , Golden Frame).
	 */
	private static boolean[] relevanceCriterionVariables(final ERelevanceStatus relevance,
			final boolean lastErrorAdmittingFlag) {
		final boolean relevanceCriterionUC;
		final boolean relevanceCriterionGF;
		final boolean relevanceCriterionDB;
		if (relevance == ERelevanceStatus.InUnsatCore) {
			// This is the case when the triple is unsatisfiable and the action is in the Unsatisfiable core.
			relevanceCriterionUC = true;
			relevanceCriterionGF = false;
			relevanceCriterionDB = false;

		} else if (relevance == ERelevanceStatus.Sat) {
			// The case when we have HAVOC statements. In this case the action is relevant if the triple is satisfiable.
			relevanceCriterionUC = false;
			relevanceCriterionGF = true;
			// if flag false at this point, that means this is the first error-admitting statement.
			relevanceCriterionDB = !lastErrorAdmittingFlag;
		} else {
			relevanceCriterionUC = false;
			relevanceCriterionGF = false;
			relevanceCriterionDB = false;
		}
		return new boolean[] { relevanceCriterionUC, relevanceCriterionGF, relevanceCriterionDB };
	}

	private void doNonFlowSensitiveAnalysis(final NestedWord<LETTER> counterexampleWord, final IPredicate truePredicate,
			final IPredicate falsePredicate, final ModifiableGlobalsTable modGlobVarManager,
			final CfgSmtToolkit csToolkit) {
		mLogger.info("Starting non-flow-sensitive error relevancy analysis");

		final FaultLocalizationRelevanceChecker rc = new FaultLocalizationRelevanceChecker(mServices, csToolkit);
		// Non-Flow Sensitive INCREMENTAL ANALYSIS

		// Calculating the WP and SP List
		final IterativePredicateTransformer iptWp = new IterativePredicateTransformer(mPredicateFactory,
				csToolkit.getManagedScript(), csToolkit.getModifiableGlobalsTable(), mServices, counterexampleWord,
				null, falsePredicate, null, mPredicateFactory.not(falsePredicate), mSimplificationTechnique,
				mXnfConversionTechnique, mSymbolTable);
		final IterativePredicateTransformer iptSp = new IterativePredicateTransformer(mPredicateFactory,
				csToolkit.getManagedScript(), csToolkit.getModifiableGlobalsTable(), mServices, counterexampleWord,
				truePredicate, null, null, mPredicateFactory.not(falsePredicate), mSimplificationTechnique,
				mXnfConversionTechnique, mSymbolTable);

		final DefaultTransFormulas dtf = new DefaultTransFormulas(counterexampleWord, truePredicate, falsePredicate,
				Collections.emptySortedMap(), csToolkit.getOldVarsAssignmentCache(), false);

		final List<IPredicatePostprocessor> postprocessors;
		if (mApplyQuantifierElimination) {
			final QuantifierEliminationPostprocessor qePostproc =
					new QuantifierEliminationPostprocessor(mServices, mLogger, csToolkit.getManagedScript(),
							mPredicateFactory, mSimplificationTechnique, mXnfConversionTechnique);
			postprocessors = Collections.singletonList(qePostproc);
		} else {
			postprocessors = Collections.emptyList();
		}
		TracePredicates weakestPreconditionSequence;
		TracePredicates strongestPostconditionSequence;
		try {
			weakestPreconditionSequence = iptWp.computeWeakestPreconditionSequence(dtf, postprocessors, true, false);
			strongestPostconditionSequence = iptSp.computeStrongestPostconditionSequence(dtf, postprocessors);
		} catch (final TraceInterpolationException e) {
			// TODO: What to do with this exception?
			throw new RuntimeException(e);
		}
		// End of the calculation

		boolean lastErrorAdmittingFlag = false;
		for (int i = counterexampleWord.length() - 1; i >= 0; i--) {
			final IAction action = counterexampleWord.getSymbol(i);
			// Calculate WP and PRE
			final IPredicate wp = weakestPreconditionSequence.getPredicate(i + 1);
			final IPredicate pre = mPredicateFactory.not(weakestPreconditionSequence.getPredicate(i));
			final IPredicate sp = strongestPostconditionSequence.getPredicate(i);
			final IPredicate intersection = mPredicateFactory.and(SimplificationTechnique.SIMPLIFY_QUICK, pre, sp);

			// Figure out what is the type of the statement (internal, call or Return)
			final ERelevanceStatus relevance;
			relevance = computeRelevance(i, action, intersection, wp, null, weakestPreconditionSequence,
					counterexampleWord, rc, csToolkit);

			final boolean[] relevanceCriterionVariables =
					relevanceCriterionVariables(relevance, lastErrorAdmittingFlag);
			final boolean relevanceCriterion1uc = relevanceCriterionVariables[0];
			final boolean relevanceCriterion1gf = relevanceCriterionVariables[1];
			final boolean relevanceCriterion3db = relevanceCriterionVariables[2];
			lastErrorAdmittingFlag |= relevanceCriterion3db; // if true, that means we already have found the last error admitting statement.
			{
				mErrorLocalizationStatisticsGenerator.reportIcfgEdge();
				if (relevanceCriterion1uc) {
					mErrorLocalizationStatisticsGenerator.reportErrorEnforcingIcfgEdge();
				}
				if (relevanceCriterion1gf) {
					mErrorLocalizationStatisticsGenerator.reportErrorAdmittingIcfgEdge();
				}
				if (!relevanceCriterion1uc && !relevanceCriterion1gf) {
					mErrorLocalizationStatisticsGenerator.reportErrorIrrelevantIcfgEdge();
				}
			}

			// Adding relevance information in the array list Relevance_of_statements.
			final RelevanceInformation ri =
					new RelevanceInformation(Collections.singletonList(action), relevanceCriterion1uc,
							relevanceCriterion1gf, ((RelevanceInformation) mRelevanceOfTrace[i]).getCriterion2UC(),
							((RelevanceInformation) mRelevanceOfTrace[i]).getCriterion2GF(), relevanceCriterion3db);

			mRelevanceOfTrace[i] = ri;
		}
		mErrorLocalizationStatisticsGenerator.addHoareTripleCheckerStatistics(rc.getHoareTripleCheckerStatistics());
		mErrorLocalizationStatisticsGenerator.reportAngelicScore(getAngelicScore());

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("- - - - - - [Non-Flow Sensitive Analysis with statments + pre/wp information]- - - - - -");
			for (int i = 0; i < counterexampleWord.length(); i++) {
				mLogger.debug(weakestPreconditionSequence.getPredicate(i));
				mLogger.debug(mRelevanceOfTrace[i]);
			}
			mLogger.debug(weakestPreconditionSequence.getPredicate(counterexampleWord.length()));
			mLogger.debug("------------------------------------------------------------------------------------------");
		}
	}

	/**
	 * Checks if sub trace from position "startPosition" to position "endPosition" is relevant.
	 */
	private boolean checkBranchRelevance(final int startPosition, final int endPosition,
			final UnmodifiableTransFormula branchEncodedFormula, final IPredicate weakestPreconditionLeft,
			final IPredicate weakestPreconditionRight, final NestedWord<LETTER> counterexampleWord,
			final CfgSmtToolkit csToolkit, final ModifiableGlobalsTable modifiableGlobalsTable,
			final TracePredicates strongestPostconditionSequence) {

		final FaultLocalizationRelevanceChecker rc = new FaultLocalizationRelevanceChecker(mServices, csToolkit);
		final IPredicate pre = mPredicateFactory.not(weakestPreconditionLeft);
		final IPredicate sp = strongestPostconditionSequence.getPredicate(startPosition);
		// Intersection of pre and sp.
		final IPredicate intersection = mPredicateFactory.and(SimplificationTechnique.SIMPLIFY_QUICK, pre, sp);
		final String preceeding = counterexampleWord.getSymbol(startPosition).getPrecedingProcedure();
		final String succeeding = counterexampleWord.getSymbol(endPosition).getSucceedingProcedure();
		final BasicInternalAction basic = new BasicInternalAction(preceeding, succeeding, branchEncodedFormula);
		// Use the pre SP intersection.
		final ERelevanceStatus relevance =
				rc.relevanceInternal(intersection, basic, mPredicateFactory.not(weakestPreconditionRight));

		return relevance == ERelevanceStatus.InUnsatCore || relevance == ERelevanceStatus.Sat;
	}

	/**
	 * Computes the corresponding branch-out position for a given branch-in position.
	 *
	 * @param branchInList
	 *            branch-in positions in descending order
	 * @return the smallest element of the branchInList that is larger than startLocation. Returns null if no such
	 *         element exists.
	 */
	private static Integer computeCorrespondingBranchOutLocation(final List<Integer> branchInList,
			final int startLocation) {
		assert branchInList != null && !branchInList.isEmpty();
		for (int i = branchInList.size() - 1; i >= 0; i--) {
			final Integer branchIn = branchInList.get(i);
			if (branchIn > startLocation) {
				branchInList.remove(i);
				return branchIn;
			}
		}
		return null;
	}

	/**
	 * Computes the Statements relevant to the flow sensitive analysis in the trace.
	 * @param postProcessedResults 
	 * @param counterexample trace
	 * @param iIcfg 
	 */
	private IPredicate computeRelevantStatements_FlowSensitive(final NestedWord<LETTER> counterexampleWord,
			final int startLocation, final int endLocation, final IPredicate weakestPreconditionBranchEndlocation,
			final PredicateTransformer<Term, IPredicate, TransFormula> pt, final FaultLocalizationRelevanceChecker rc,
			final CfgSmtToolkit csToolkit, final ModifiableGlobalsTable modifiableGlobalsTable,
			final TracePredicates strongestPostconditionSequence, Map<Integer, Map<Integer, Set<IcfgEdge>>> postProcessedResults, 
			final NestedRun<LETTER,IPredicate> counterexample, final IIcfg<IcfgLocation> IIcfg) {
		IPredicate weakestPreconditionLeft = weakestPreconditionBranchEndlocation;
		for (int position = endLocation; position >= startLocation; position--) {
			final LETTER statement = counterexampleWord.getSymbol(position);
			
			final Map<Integer, Set<IcfgEdge>> branchIn = postProcessedResults.get(position);
			Integer branchOutPosition = null;
			Set<IcfgEdge> subGraphEdges = null;
			UnmodifiableTransFormula mergedFormula = null;
			if(branchIn != null && !branchIn.isEmpty()) {
				final ArrayList<Integer> branchIn2 = new ArrayList<>(branchIn.keySet());
				branchIn2.sort(Collections.reverseOrder());
				branchOutPosition = computeCorrespondingBranchOutLocation(branchIn2, startLocation);
				subGraphEdges = branchIn.get(branchOutPosition);
				
			} else {
				branchOutPosition = null;
			}
			final IPredicate weakestPreconditionRight = weakestPreconditionLeft;
			if(branchOutPosition != null) {
				branchIn.remove(branchOutPosition);
				final int positionBranchIn = position;
				
				mergedFormula = constructConglomerate(branchOutPosition, position, subGraphEdges, counterexample, IIcfg);
				position = branchOutPosition;
				final Term wpTerm = computeWp(weakestPreconditionRight, mergedFormula,
						csToolkit.getManagedScript().getScript(), csToolkit.getManagedScript(), pt,
						mApplyQuantifierElimination);
				weakestPreconditionLeft = mPredicateFactory.newPredicate(wpTerm);
				final boolean isRelevant = checkBranchRelevance(branchOutPosition, positionBranchIn,
						mergedFormula, weakestPreconditionLeft, weakestPreconditionRight,
						counterexampleWord, csToolkit, modifiableGlobalsTable, strongestPostconditionSequence);
				if (isRelevant) {
					// If the branch is Relevant. Recursion
					weakestPreconditionLeft = computeRelevantStatements_FlowSensitive(counterexampleWord,
							branchOutPosition, positionBranchIn, weakestPreconditionRight, pt, rc, csToolkit,
							modifiableGlobalsTable, strongestPostconditionSequence,
							postProcessedResults, counterexample, IIcfg);
					// If the branch is relevant, then the wp should come from inside the branch.
					// That is why weakestPreconditionLeft is coming from inside the branch now.
				} else {
					// Don't do anything.
					mLogger.debug(
							" - - Irrelevant Branch - - - [BlockEncodedFormula:" + mergedFormula + " ]");
				}

			} else {
				// The statement is NOT a BRANCH-IN Statement.

				final UnmodifiableTransFormula tf = counterexampleWord.getSymbol(position).getTransformula();
				final Term wpTerm = computeWp(weakestPreconditionRight, tf, csToolkit.getManagedScript().getScript(),
						csToolkit.getManagedScript(), pt, mApplyQuantifierElimination);
				weakestPreconditionLeft = mPredicateFactory.newPredicate(wpTerm);
				final IPredicate pre = mPredicateFactory.not(weakestPreconditionLeft);
				final IPredicate sp = strongestPostconditionSequence.getPredicate(position);
				// use pre sp intersection.
				final IPredicate intersection = mPredicateFactory.and(SimplificationTechnique.SIMPLIFY_QUICK, pre, sp);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(" ");
					mLogger.debug("WP -- > " + weakestPreconditionRight);
					mLogger.debug(" Statement -- > " + statement);
					mLogger.debug("Pre --> " + pre);
					mLogger.debug("Sp -- >" + sp);
					mLogger.debug("intersection -- >" + intersection);
					mLogger.debug(" ");
				}
				final IAction action = counterexampleWord.getSymbol(position);
				final ERelevanceStatus relevance = computeRelevance(position, action, intersection,
						weakestPreconditionRight, weakestPreconditionLeft, null, counterexampleWord, rc, csToolkit);
				final boolean[] relevanceCriterionVariables = relevanceCriterionVariables(relevance, false);
				final boolean relevanceCriterion2uc = relevanceCriterionVariables[0];
				final boolean relevanceCriterion2gf = relevanceCriterionVariables[1];
				// Report statistics
				{
					mErrorLocalizationStatisticsGenerator.reportIcfgEdge();
					if (relevanceCriterion2uc) {
						mErrorLocalizationStatisticsGenerator.reportErrorEnforcingIcfgEdge();
					}
					if (relevanceCriterion2gf) {
						mErrorLocalizationStatisticsGenerator.reportErrorAdmittingIcfgEdge();
					}
					if (!relevanceCriterion2uc && !relevanceCriterion2gf) {
						mErrorLocalizationStatisticsGenerator.reportErrorIrrelevantIcfgEdge();
					}
				}
				final RelevanceInformation ri = new RelevanceInformation(Collections.singletonList(action),
						((RelevanceInformation) mRelevanceOfTrace[position]).getCriterion1UC(),
						((RelevanceInformation) mRelevanceOfTrace[position]).getCriterion1GF(), relevanceCriterion2uc,
						relevanceCriterion2gf, false);
				mRelevanceOfTrace[position] = ri;
			}
		}
		mErrorLocalizationStatisticsGenerator.addHoareTripleCheckerStatistics(rc.getHoareTripleCheckerStatistics());
		return weakestPreconditionLeft;
	}

	/**
	 * Computes the relevance information of a position in the trace, depending on the type of the codeblock at that
	 * location. (IInternalAction, ICallAction, IReturnAction).
	 *
	 * @return Relevance Information of a position in the trace.
	 */
	private ERelevanceStatus computeRelevance(final int position, final IAction action, final IPredicate pre,
			final IPredicate weakestPreconditionRight, final IPredicate weakestPreconditionLeft,
			final TracePredicates weakestPreconditionSequence, final NestedWord<LETTER> counterexampleWord,
			final FaultLocalizationRelevanceChecker rc, final CfgSmtToolkit csToolkit) {
		ERelevanceStatus relevance;
		if (action instanceof IInternalAction) {
			final IInternalAction internal = (IInternalAction) counterexampleWord.getSymbol(position);
			relevance = rc.relevanceInternal(pre, internal, mPredicateFactory.not(weakestPreconditionRight));
		} else if (action instanceof ICallAction) {
			final ICallAction call = (ICallAction) counterexampleWord.getSymbol(position);
			relevance = rc.relevanceCall(pre, call, mPredicateFactory.not(weakestPreconditionRight));
		} else if (action instanceof IReturnAction) {
			final IReturnAction ret = (IReturnAction) counterexampleWord.getSymbol(position);
			assert counterexampleWord.isReturnPosition(position);
			assert !counterexampleWord.isPendingReturn(position) : "pending returns not supported";
			final IPredicate callPredecessor;
			if (weakestPreconditionSequence != null) {
				// In case of Non-FlowSensitive
				final int callPos = counterexampleWord.getCallPosition(position);
				callPredecessor = weakestPreconditionSequence.getPredicate(callPos);
			} else {
				// In case of FlowSensitive.
				callPredecessor = weakestPreconditionLeft;
			}

			relevance = rc.relevanceReturn(pre, callPredecessor, ret, mPredicateFactory.not(weakestPreconditionRight));
		} else {
			throw new AssertionError("Unknown Action " + action.getClass().getSimpleName());
		}
		return relevance;
	}

	/**
	 * Compute WP and optionally apply quantifier elimination.
	 */
	private Term computeWp(final IPredicate successor, final UnmodifiableTransFormula tf, final Script script,
			final ManagedScript freshTermVariableConstructor,
			final PredicateTransformer<Term, IPredicate, TransFormula> pt, final boolean applyQuantifierElimination) {
		Term result = pt.weakestPrecondition(successor, tf);
		if (applyQuantifierElimination) {
			result = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, freshTermVariableConstructor,
					result, mSimplificationTechnique, mXnfConversionTechnique);
		}
		return result;
	}

	private void doFlowSensitiveAnalysis(final NestedRun<LETTER, IPredicate> counterexample,
			final IPredicate truePredicate, final INestedWordAutomaton<LETTER, IPredicate> cfg,
			final ModifiableGlobalsTable modifiableGlobalsTable, final CfgSmtToolkit csToolkit, IIcfg<IcfgLocation> IIcfg) {
		mLogger.info("Starting flow-sensitive error relevancy analysis");
		

		
		// get information from CFG but instead of fromulas, put edges
		final Map<Integer, Map<Integer, Set<IcfgEdge>>> informationFromCfg2 =
				computeInformationFromCFG(counterexample, cfg, csToolkit.getManagedScript());
		
		// Post process branching informations
		final Map<Integer, Map<Integer, Set<IcfgEdge>>> postProcessedResults = postProcessInformationFromCFG(counterexample, informationFromCfg2, 
				0, counterexample.getLength()-1);
		
		// Count branches in the trace.
		int numberOfBranches = 0;
		final Collection<Map<Integer, Set<IcfgEdge>>> listOfValues = postProcessedResults.values();
		for (final Map<Integer, Set<IcfgEdge>> onelist : listOfValues) {
			numberOfBranches += onelist.values().size();
		}
		mErrorLocalizationStatisticsGenerator.reportNumberOfBranches(numberOfBranches);
		// You should send the counter example, the CFG information and the the start of the branch and the end of the
		// branch.
		final PredicateTransformer<Term, IPredicate, TransFormula> pt = new PredicateTransformer<>(
				csToolkit.getManagedScript(), new TermDomainOperationProvider(mServices, csToolkit.getManagedScript()));
		final FaultLocalizationRelevanceChecker rc = new FaultLocalizationRelevanceChecker(mServices, csToolkit);
		final int startLocation = 0;
		final int endLocation = counterexample.getWord().length() - 1;
		final IPredicate falsePredicate =
				mPredicateFactory.newPredicate(csToolkit.getManagedScript().getScript().term("false"));

		// Calculating the SP List
		final IterativePredicateTransformer iptSp = new IterativePredicateTransformer(mPredicateFactory,
				csToolkit.getManagedScript(), csToolkit.getModifiableGlobalsTable(), mServices,
				counterexample.getWord(), truePredicate, null, null, mPredicateFactory.not(falsePredicate),
				mSimplificationTechnique, mXnfConversionTechnique, mSymbolTable);

		final DefaultTransFormulas dtf = new DefaultTransFormulas(counterexample.getWord(), truePredicate,
				falsePredicate, Collections.emptySortedMap(), csToolkit.getOldVarsAssignmentCache(), false);

		final List<IPredicatePostprocessor> postprocessors;
		if (mApplyQuantifierElimination) {
			final QuantifierEliminationPostprocessor qePostproc =
					new QuantifierEliminationPostprocessor(mServices, mLogger, csToolkit.getManagedScript(),
							mPredicateFactory, mSimplificationTechnique, mXnfConversionTechnique);
			postprocessors = Collections.singletonList(qePostproc);
		} else {
			postprocessors = Collections.emptyList();
		}
		TracePredicates strongestPostconditionSequence;
		strongestPostconditionSequence = iptSp.computeStrongestPostconditionSequence(dtf, postprocessors);

		// End of the calculation

		computeRelevantStatements_FlowSensitive(counterexample.getWord(), startLocation, endLocation, falsePredicate,
				pt, rc, csToolkit, modifiableGlobalsTable, strongestPostconditionSequence, postProcessedResults,
				counterexample, IIcfg);
		mErrorLocalizationStatisticsGenerator.reportAngelicScore(getAngelicScore());
	}

	/**
	 * Check if there is a path from startPoint so some element of the possibleEndPoints set. If yes, a NestedRun is
	 * returned, otherwise null is returned.
	 */
	private NestedRun<LETTER, IPredicate> findPathInCfg(final IPredicate startPoint, final IPredicate parentState,
			final Set<IPredicate> possibleEndPoints, final INestedWordAutomaton<LETTER, IPredicate> cfg) {
		try {
			return new IsEmpty<>(new AutomataLibraryServices(mServices), cfg, Collections.singleton(startPoint),
					Collections.singleton(parentState), possibleEndPoints).getNestedRun();
		} catch (final AutomataOperationCanceledException e) {
			final RunningTaskInfo runningTaskInfo = new RunningTaskInfo(getClass(), null);
			throw new ToolchainCanceledException(e, runningTaskInfo);
		}
	}

	/**
	 * @return List of {@link RelevanceInformation}s one for each LETTER in the counterexample.
	 */
	public List<IRelevanceInformation> getRelevanceInformation() {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("- - - - - - - -");
			for (int i = 0; i < mRelevanceOfTrace.length; i++) {
				mLogger.debug(((RelevanceInformation) mRelevanceOfTrace[i]).getActions() + " | "
						+ mRelevanceOfTrace[i].getShortString());
			}
		}
		return Arrays.asList(mRelevanceOfTrace);
	}

	/**
	 * @return Statistics object.
	 */
	public ErrorLocalizationStatisticsGenerator getStatistics() {
		return mErrorLocalizationStatisticsGenerator;
	}

	/**
	 * Check if the trace (the assertion failure) is angelically safe, based on our definition of angelic safety via
	 * aberrant trace elements.
	 *
	 * @return Boolean value, determining if the trace is angelically safe.
	 */
	public Boolean getAngelicStatus() {
		// Check that all elements of the trace are
		// only error-admitting.
		// Return false even if a single trace element is error enforcing.

		Boolean angelicStatus = false;
		for (int i = 0; i < mRelevanceOfTrace.length; i++) {
			if (((RelevanceInformation) mRelevanceOfTrace[i]).getCriterion2UC()) {
				return false;
			}
			angelicStatus |= ((RelevanceInformation) mRelevanceOfTrace[i]).getCriterion2GF();
		}
		return angelicStatus;
	}
	
	/** Return the Angelic score of an error trace and hence
	 * the assertion violation.
	 * A score of 1 means it is highly "interesting" for the
	 * user from a debugging point of view.
	 * 
	 * A score of 0 would mean that the assertion violation
	 * is totally dependent on the values coming from the 
	 * environment.
	 * 
	 * @return double, The rank of the trace between  0 and 1.
	 */
	private double getAngelicScore() {
		double angelicScore = 0;
		int numberOfAberrantStatements = 0;
		int totalNumberofAberrantStatements = 0;
		for (int i = 0; i < mRelevanceOfTrace.length; i++) {
			if (((RelevanceInformation) mRelevanceOfTrace[i]).getCriterion2UC() || 
					((RelevanceInformation) mRelevanceOfTrace[i]).getCriterion1UC()) {
				numberOfAberrantStatements++;
				totalNumberofAberrantStatements++;
			} else if(((RelevanceInformation) mRelevanceOfTrace[i]).getCriterion2GF() ||
					((RelevanceInformation) mRelevanceOfTrace[i]).getCriterion1GF()) {
				totalNumberofAberrantStatements++;
			}
		}
		if(totalNumberofAberrantStatements != 0){ 
			angelicScore = (double) numberOfAberrantStatements / totalNumberofAberrantStatements;
			 
			 }
		return angelicScore;
	}
}
