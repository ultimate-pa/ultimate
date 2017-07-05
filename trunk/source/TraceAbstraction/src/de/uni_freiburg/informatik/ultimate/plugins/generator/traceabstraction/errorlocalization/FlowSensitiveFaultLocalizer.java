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
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.RelevanceInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.FaultLocalizationRelevanceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.FaultLocalizationRelevanceChecker.ERelevanceStatus;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.IPredicatePostprocessor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.QuantifierEliminationPostprocessor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.TraceInterpolationException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.DefaultTransFormulas;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TracePredicates;
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
			final boolean doNonFlowSensitiveAnalysis, final boolean doFlowSensitiveAnalysis,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final IIcfgSymbolTable symbolTable) {
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
			if (doNonFlowSensitiveAnalysis) {
				doNonFlowSensitiveAnalysis(counterexample.getWord(),predicateUnifier.getTruePredicate(),
						predicateUnifier.getFalsePredicate(), modifiableGlobalsTable, csToolkit);
			}

			if (doFlowSensitiveAnalysis) {
				doFlowSensitiveAnalysis(counterexample, cfg, modifiableGlobalsTable, csToolkit);
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
					Collections.singletonList(counterexampleWord.getSymbolAt(i)), false, false, false, false);
			result[i] = relevancyOfAction;
		}
		return result;
	}

	/**
	 * Compute branch-in and branch-out information from cfg.
	 *
	 * @return List of pairs, where each pair encodes an alternative path (a path of cfg that is not part of the trace).
	 *         If the pair (k,j) is in the list this means that there is an alternative path from position k to position
	 *         j in the trace.
	 */
	private Map<Integer, List<Integer>> computeInformationFromCfg(final NestedRun<LETTER, IPredicate> counterexample,
			final INestedWordAutomaton<LETTER, IPredicate> cfg) {
		// TODO: result of alternative computation, only used for debugging
		final List<int[]> resultOld = new ArrayList<>();

		// Using Better Data Structure to save graph information.
		final Map<Integer, List<Integer>> result = new HashMap<>();

		// Create a Map of Programpoints in the CFG to States of the CFG.
		final Map<IcfgLocation, IPredicate> programPointToState = new HashMap<>();
		for (final IPredicate cfgState : cfg.getStates()) {
			final ISLPredicate islState = (ISLPredicate) cfgState;
			final IcfgLocation programPoint = islState.getProgramPoint();
			programPointToState.put(programPoint, cfgState);
		}

		// For each state find out if it's a branch or not.
		// For each state, find out if there is an outgoing branch from that state
		// that transitions to a state which is not in the counter example.
		// if you find such a state, then from that state. run the FINDPATHINCFG() method
		// and find out if that path returns to a state which IS in the counterexample.
		// If you find such a path, then that state is a branching state then you save this information for future use.
		for (int posOfStartState = 0; posOfStartState < counterexample.getLength() - 1; posOfStartState++) {
			// State in consideration at the moment.
			final IPredicate startStateInTrace = counterexample.getStateAtPosition(posOfStartState);
			// Program point of the state under consideration.final
			final IcfgLocation programpointOfStartStateInTrace = ((ISLPredicate) startStateInTrace).getProgramPoint();

			// the startStateInCfg will be forbidden in the alternative path (FORBIDDEN STATE BUG)
			final IPredicate startStateInCfg = programPointToState.get(programpointOfStartStateInTrace);

			final Set<IPredicate> possibleEndPoints =
					computePossibleEndpoints(counterexample, programPointToState, posOfStartState);

			final IcfgLocation programPointOfSuccInCounterexample =
					((ISLPredicate) counterexample.getStateAtPosition(posOfStartState + 1)).getProgramPoint();
			// Immediate successors of of the state in CFG
			final Iterable<OutgoingInternalTransition<LETTER, IPredicate>> immediateSuccesors =
					cfg.internalSuccessors(startStateInCfg);
			for (final OutgoingInternalTransition<LETTER, IPredicate> transition : immediateSuccesors) {
				final IPredicate immediateSuccesor = transition.getSucc();
				final IcfgLocation programPointOfImmediateSucc = ((ISLPredicate) immediateSuccesor).getProgramPoint();
				if (programPointOfImmediateSucc == programPointOfSuccInCounterexample) {
					// do nothing, because we want to find an alternative path
					// (i.e., path that is not in counterexample
				} else {
					// For Branch in Branch Out information.
					// Path from the successor state not in the counter example
					// to one of the states in possibleEndPoints.
					final NestedRun<LETTER, IPredicate> alternativePath =
							findPathInCfg(immediateSuccesor, startStateInCfg, possibleEndPoints, cfg);
					if (alternativePath != null) {
						// If such a path exists. Then that means that there is a path from the successor state
						// that comes back to the counter example
						// THAT MEANS WE HAVE FOUND AN out-BRANCH AT POSITION "COUNTER"
						final IPredicate lastStateOfAlternativePath =
								alternativePath.getStateAtPosition(alternativePath.getLength() - 1);

						final List<Integer> endPosition = computeEndpointOfAlternativePath(counterexample,
								posOfStartState, lastStateOfAlternativePath);

						for (final Integer i : endPosition) {
							final int[] pair = new int[2];
							// position OUT-BRANCH in the counterexample.
							pair[0] = posOfStartState;
							pair[1] = i - 1;
							resultOld.add(pair);

							// If the Branch-In Location is not in the map, then add it.
							if (result.get(i - 1) == null) {
								final List<Integer> branchInPosArray = new ArrayList<>();
								branchInPosArray.add(posOfStartState);
								result.put(i - 1, branchInPosArray);
							} else {
								// It is in the map,
								result.get(i - 1).add(posOfStartState);
								// The array should be in descending order, so we can delete
								// the elements from this array more efficiently.
								result.get(i - 1).sort(Collections.reverseOrder());
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
	private static boolean[] relevanceCriterionVariables(final ERelevanceStatus relevance) {
		final boolean relevanceCriterionUC;
		final boolean relevanceCriterionGF;
		if (relevance == ERelevanceStatus.InUnsatCore) {
			// This is the case when the triple is unsatisfiable and the action is in the Unsatisfiable core.
			relevanceCriterionUC = true;
			relevanceCriterionGF = false;

		} else if (relevance == ERelevanceStatus.Sat) {
			// The case when we have HAVOC statements. In this case the action is relevant if the triple is satisfiable.
			relevanceCriterionUC = false;
			relevanceCriterionGF = true;
		} else {
			relevanceCriterionUC = false;
			relevanceCriterionGF = false;
		}
		return new boolean[] { relevanceCriterionUC, relevanceCriterionGF };
	}

	private void doNonFlowSensitiveAnalysis(final NestedWord<LETTER> counterexampleWord, final IPredicate truePredicate,
			final IPredicate falsePredicate, final ModifiableGlobalsTable modGlobVarManager,
			final CfgSmtToolkit csToolkit) {
		mLogger.info("Starting non-flow-sensitive error relevancy analysis");

		final FaultLocalizationRelevanceChecker rc = new FaultLocalizationRelevanceChecker(csToolkit);
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
		
		for (int i = counterexampleWord.length() - 1; i >= 0; i--) {
			final IAction action = counterexampleWord.getSymbolAt(i);
			// Calculate WP and PRE
			final IPredicate wp = weakestPreconditionSequence.getPredicate(i + 1);
			final IPredicate pre = mPredicateFactory.not(weakestPreconditionSequence.getPredicate(i));
			final IPredicate sp = strongestPostconditionSequence.getPredicate(i);
			final IPredicate intersection = mPredicateFactory.and(SimplificationTechnique.SIMPLIFY_QUICK, pre,sp);

			// Figure out what is the type of the statement (internal, call or Return)
			final ERelevanceStatus relevance;
			relevance = computeRelevance(i, action, intersection, wp, null, weakestPreconditionSequence, counterexampleWord, rc,
					csToolkit);

			final boolean[] relevanceCriterionVariables = relevanceCriterionVariables(relevance);
			final boolean relevanceCriterion1uc = relevanceCriterionVariables[0];
			final boolean relevanceCriterion1gf = relevanceCriterionVariables[1];
			{
				mErrorLocalizationStatisticsGenerator.reportIcfgEdge();
				if (relevanceCriterion1uc) {
					mErrorLocalizationStatisticsGenerator.reportErrorEnforcingIcfgEdge();
				}
				if (relevanceCriterion1gf) {
					mErrorLocalizationStatisticsGenerator.reportErrorAdmittingIcfgEdge();
				}
				if (!relevanceCriterion1uc && !relevanceCriterion1uc) {
					mErrorLocalizationStatisticsGenerator.reportErrorIrrelevantIcfgEdge();
				}
			}

			// Adding relevance information in the array list Relevance_of_statements.
			final RelevanceInformation ri =
					new RelevanceInformation(Collections.singletonList(action), relevanceCriterion1uc,
							relevanceCriterion1gf, ((RelevanceInformation) mRelevanceOfTrace[i]).getCriterion2UC(),
							((RelevanceInformation) mRelevanceOfTrace[i]).getCriterion2GF());

			mRelevanceOfTrace[i] = ri;
		}
		mErrorLocalizationStatisticsGenerator.addHoareTripleCheckerStatistics(rc.getHoareTripleCheckerStatistics());

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
	 * Recursively Compute the Markhor Formula of a branch.
	 *
	 * @param startPosition
	 *            - Starting location of the branch.
	 * @param endPosition
	 *            - End location of the branch.
	 */
	private UnmodifiableTransFormula computeMarkhorFormula(final int startPosition, final int endPosition,
			final NestedWord<LETTER> counterexampleWord, final Map<Integer, List<Integer>> informationFromCfg,
			final ManagedScript csToolkit) {
		UnmodifiableTransFormula combinedTransitionFormula =
				counterexampleWord.getSymbolAt(startPosition).getTransformula();
		for (int i = startPosition + 1; i <= endPosition; i++) {
			boolean subBranch = false;
			int branchOut = 0;
			int branchIn = 0;
			// Find out if the current position is a branchOut position.
			for (final Entry<Integer, List<Integer>> entry : informationFromCfg.entrySet()) {
				if (entry.getValue().contains(i)) {
					subBranch = true;
					branchOut = i;
					final Integer brachInPosition = entry.getKey();
					branchIn = brachInPosition - 1;
					i = branchIn;
					break;
				}
			}
			if (subBranch) {
				// The current statement is a branch out and it's branch-in is with in the current branch.
				final UnmodifiableTransFormula subBranchMarkhorFormula =
						computeMarkhorFormula(branchOut, branchIn, counterexampleWord, informationFromCfg, csToolkit);
				combinedTransitionFormula = TransFormulaUtils.sequentialComposition(mLogger, mServices, csToolkit,
						false, false, false, mXnfConversionTechnique, mSimplificationTechnique, Arrays.asList(
								new UnmodifiableTransFormula[] { combinedTransitionFormula, subBranchMarkhorFormula }));
			} else {
				// It is a normal statement.
				final LETTER statement = counterexampleWord.getSymbol(i);
				final UnmodifiableTransFormula transitionFormula = statement.getTransformula();
				combinedTransitionFormula = TransFormulaUtils.sequentialComposition(mLogger, mServices, csToolkit,
						false, false, false, mXnfConversionTechnique, mSimplificationTechnique,
						Arrays.asList(new UnmodifiableTransFormula[] { combinedTransitionFormula, transitionFormula }));
			}
		}
		return TransFormulaUtils.computeMarkhorTransFormula(combinedTransitionFormula, csToolkit, mServices, mLogger,
				mXnfConversionTechnique, mSimplificationTechnique);
	}

	/**
	 * Checks if subtrace from position "startPosition" to position "endPosition" is relevant.
	 */
	private boolean checkBranchRelevance(final int startPosition, final int endPosition,
			final UnmodifiableTransFormula markhor, final IPredicate weakestPreconditionLeft,
			final IPredicate weakestPreconditionRight, final NestedWord<LETTER> counterexampleWord,
			final CfgSmtToolkit csToolkit, final ModifiableGlobalsTable modifiableGlobalsTable) {

		final FaultLocalizationRelevanceChecker rc = new FaultLocalizationRelevanceChecker(csToolkit);
		final IPredicate pre = mPredicateFactory.not(weakestPreconditionLeft);
		final String preceeding = counterexampleWord.getSymbolAt(startPosition).getPrecedingProcedure();
		final String succeeding = counterexampleWord.getSymbolAt(endPosition).getSucceedingProcedure();
		final BasicInternalAction basic = new BasicInternalAction(preceeding, succeeding, markhor);
		final ERelevanceStatus relevance =
				rc.relevanceInternal(pre, basic, mPredicateFactory.not(weakestPreconditionRight));

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
	 */
	private void computeRelevantStatements_FlowSensitive(final NestedWord<LETTER> counterexampleWord,
			final int startLocation, final int endLocation, final IPredicate weakestPreconditionBranchEndlocation,
			final PredicateTransformer pt, final FaultLocalizationRelevanceChecker rc, final CfgSmtToolkit csToolkit,
			final ModifiableGlobalsTable modifiableGlobalsTable, final Map<Integer, List<Integer>> informationFromCfg) {
		IPredicate weakestPreconditionLeft = weakestPreconditionBranchEndlocation;
		for (int position = endLocation; position >= startLocation; position--) {
			final LETTER statement = counterexampleWord.getSymbol(position);

			final List<Integer> branchIn = informationFromCfg.get(position);
			final Integer branchOutPosition;
			if (branchIn != null && !branchIn.isEmpty()) {
				// Branch IN Statement
				branchOutPosition = computeCorrespondingBranchOutLocation(branchIn, startLocation);
			} else {
				branchOutPosition = null;
			}
			final IPredicate weakestPreconditionRight = weakestPreconditionLeft;
			if (branchOutPosition != null) {
				final int positionBranchIn = position;
				position = branchOutPosition;
				final UnmodifiableTransFormula markhor = computeMarkhorFormula(branchOutPosition, positionBranchIn,
						counterexampleWord, informationFromCfg, csToolkit.getManagedScript());
				final Term wpTerm =
						computeWp(weakestPreconditionRight, markhor, csToolkit.getManagedScript().getScript(),
								csToolkit.getManagedScript(), pt, mApplyQuantifierElimination);
				weakestPreconditionLeft = mPredicateFactory.newPredicate(wpTerm);
				// Check the relevance of the branch.
				final boolean isRelevant =
						checkBranchRelevance(branchOutPosition, positionBranchIn, markhor, weakestPreconditionLeft,
								weakestPreconditionRight, counterexampleWord, csToolkit, modifiableGlobalsTable);
				if (isRelevant) {
					// If the branch is Relevant. Recursion
					computeRelevantStatements_FlowSensitive(counterexampleWord, branchOutPosition, positionBranchIn,
							weakestPreconditionRight, pt, rc, csToolkit, modifiableGlobalsTable, informationFromCfg);
				} else {
					// Don't do anything.
					mLogger.debug(" - - Irrelevant Branch - - - [MarkhorFormula:" + markhor + " ]");
				}

			} else {
				// The statement under consideration is NOT a BRANCH-IN Statement.

				final UnmodifiableTransFormula tf = counterexampleWord.getSymbolAt(position).getTransformula();
				final Term wpTerm = computeWp(weakestPreconditionRight, tf, csToolkit.getManagedScript().getScript(),
						csToolkit.getManagedScript(), pt, mApplyQuantifierElimination);
				weakestPreconditionLeft = mPredicateFactory.newPredicate(wpTerm);
				final IPredicate pre = mPredicateFactory.not(weakestPreconditionLeft);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(" ");
					mLogger.debug("WP -- > " + weakestPreconditionRight);
					mLogger.debug(" Statement -- > " + statement);
					mLogger.debug("Pre --> " + pre);
					mLogger.debug(" ");
				}
				final IAction action = counterexampleWord.getSymbolAt(position);
				final ERelevanceStatus relevance = computeRelevance(position, action, pre, weakestPreconditionRight,
						weakestPreconditionLeft, null, counterexampleWord, rc, csToolkit);
				final boolean[] relevanceCriterionVariables = relevanceCriterionVariables(relevance);
				final boolean relevanceCriterion2uc = relevanceCriterionVariables[0];
				final boolean relevanceCriterion2gf = relevanceCriterionVariables[1];
				final RelevanceInformation ri = new RelevanceInformation(Collections.singletonList(action),
						((RelevanceInformation) mRelevanceOfTrace[position]).getCriterion1UC(),
						((RelevanceInformation) mRelevanceOfTrace[position]).getCriterion1GF(), relevanceCriterion2uc,
						relevanceCriterion2gf);
				mRelevanceOfTrace[position] = ri;
			}
		}
	}

	/**
	 * Computes the relevance information of a position in the trace, depending on the type of the codeblock at that
	 * location. (IInternalAction, ICallAction, IReturnAction).
	 *
	 * @return Relevance Information of a position in the trace.
	 */
	private ERelevanceStatus computeRelevance(final int position, final IAction action, final IPredicate pre,
			final IPredicate weakestPreconditionRight, final IPredicate weakestPreconditionLeft,
			final TracePredicates weakestPreconditionSequence,
			final NestedWord<LETTER> counterexampleWord, final FaultLocalizationRelevanceChecker rc,
			final CfgSmtToolkit csToolkit) {
		ERelevanceStatus relevance;
		if (action instanceof IInternalAction) {
			final IInternalAction internal = (IInternalAction) counterexampleWord.getSymbolAt(position);
			relevance = rc.relevanceInternal(pre, internal, mPredicateFactory.not(weakestPreconditionRight));
		} else if (action instanceof ICallAction) {
			final ICallAction call = (ICallAction) counterexampleWord.getSymbolAt(position);
			relevance = rc.relevanceCall(pre, call, mPredicateFactory.not(weakestPreconditionRight));
		} else if (action instanceof IReturnAction) {
			final IReturnAction ret = (IReturnAction) counterexampleWord.getSymbolAt(position);
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
			final ManagedScript freshTermVariableConstructor, final PredicateTransformer<Term, IPredicate, TransFormula> pt,
			final boolean applyQuantifierElimination) {
		Term result = pt.weakestPrecondition(successor, tf);
		if (applyQuantifierElimination) {
			result = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, freshTermVariableConstructor,
					result, mSimplificationTechnique, mXnfConversionTechnique);
		}
		return result;
	}

	private void doFlowSensitiveAnalysis(final NestedRun<LETTER, IPredicate> counterexample,
			final INestedWordAutomaton<LETTER, IPredicate> cfg, final ModifiableGlobalsTable modifiableGlobalsTable,
			final CfgSmtToolkit csToolkit) {
		mLogger.info("Starting flow-sensitive error relevancy analysis");
		final Map<Integer, List<Integer>> informationFromCfg = computeInformationFromCfg(counterexample, cfg);
		// You should send the counter example, the CFG information and the the start of the branch and the end of the
		// branch.
		final PredicateTransformer<Term, IPredicate, TransFormula> pt = new PredicateTransformer<>(
				csToolkit.getManagedScript(), new TermDomainOperationProvider(mServices, csToolkit.getManagedScript()));
		final FaultLocalizationRelevanceChecker rc = new FaultLocalizationRelevanceChecker(csToolkit);
		final int startLocation = 0;
		final int endLocation = counterexample.getWord().length() - 1;
		final IPredicate falsePredicate =
				mPredicateFactory.newPredicate(csToolkit.getManagedScript().getScript().term("false"));

		computeRelevantStatements_FlowSensitive(counterexample.getWord(), startLocation, endLocation, falsePredicate,
				pt, rc, csToolkit, modifiableGlobalsTable, informationFromCfg);
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
}
