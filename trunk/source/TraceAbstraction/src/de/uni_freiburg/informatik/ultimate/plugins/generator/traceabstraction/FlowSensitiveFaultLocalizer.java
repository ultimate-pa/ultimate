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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.results.IRelevanceInformation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.FaultLocalizationRelevanceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.FaultLocalizationRelevanceChecker.ERelevanceStatus;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.PredicatePostprocessor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.QuantifierEliminationPostprocessor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.DefaultTransFormulas;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;
/**
 * Relevance information of a trace. Used to compute the relevant statements 
 * in an Error trace that are relevant (or responsible) for the reaching the 
 * error trace according to some Error Relevance criterion. Currently we have 
 * two relevance criterion 
 * 1) Non-Flow Sensitive 
 * 2) Flow Sensitive.
 * 
 * @author Numair Mansur
 * @author Matthias Heizmann
 * @author Christian Schilling
 * 
 *
 */
public class FlowSensitiveFaultLocalizer {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final IRelevanceInformation[] mRelevanceOfTrace;
	/**
	 * Apply quantifier elimination during the computation of pre and wp.
	 * If set to true, there is a higher risk that we run into a timeout.
	 * If set to false, there is a higher risk that the SMT solver returns 
	 * unknown.
	 */
	private final boolean mApplyQuantifierElimination = true;

	public FlowSensitiveFaultLocalizer(IRun<CodeBlock, IPredicate> counterexample,
			INestedWordAutomaton<CodeBlock, IPredicate> cfg, IUltimateServiceProvider services,
			SmtManager smtManager,
			ModifiableGlobalVariableManager modGlobVarManager, PredicateUnifier predicateUnifier) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mRelevanceOfTrace = initializeRelevanceOfTrace(counterexample);

		doNonFlowSensitiveAnalysis((NestedWord<CodeBlock>) counterexample.getWord(),
				predicateUnifier.getFalsePredicate(), modGlobVarManager, smtManager);

		doFlowSensitiveAnalysis((NestedRun<CodeBlock, IPredicate>) counterexample, cfg,
				modGlobVarManager, smtManager);
	}
	


	/**
	 * Construct RelevanceInformation array for trace.
	 * @return array with empty IRelevanceInformation for each IAction in the trace.
	 */
	private IRelevanceInformation[] initializeRelevanceOfTrace(final IRun<CodeBlock, IPredicate> counterexampleRun){
		final IRelevanceInformation[] result = new IRelevanceInformation[counterexampleRun.getLength() - 1];
		final NestedWord<CodeBlock> counterexampleWord = (NestedWord<CodeBlock>) counterexampleRun.getWord();
		for(int i = 0; i<counterexampleWord.length(); i++){
			final IRelevanceInformation relevancyOfAction = new RelevanceInformation(
					Collections.singletonList(counterexampleWord.getSymbolAt(i)), false, false, false, false);
			result[i] = relevancyOfAction;
		}
		return result;
	}
	
	
	/**
	 * Compute branch-in and branch-out information from cfg.
	 *  @param counterexample
	 * @param cfg
	 * @return List of pairs, where each pair encodes an alternative path
	 * (a path of cfg that is not part of the trace). If the pair (k,j) is
	 * in the list this means that there is an alternative path from
	 * position k to position j in the trace.
	 */
	private Map<Integer, List<Integer>> computeInformationFromCFG(
			final NestedRun<CodeBlock, IPredicate> counterexample,
			final INestedWordAutomaton<CodeBlock, IPredicate> cfg){
		//TODO: result of alternative computation, only used for debugging
		final List<int[]> result_Old = new ArrayList<>();
		
		//Using Better Data Structure to save graph information. 
		final Map<Integer, List<Integer>> result = new HashMap<Integer, List<Integer>>();

		
		// Create a Map of Programpoints in the CFG to States of the CFG.
		final Map <ProgramPoint,IPredicate> programPoint_StateMap = new HashMap<>();
		for (final IPredicate cfgState : cfg.getStates()) {
			final ISLPredicate islState  = (ISLPredicate) cfgState;
			final ProgramPoint programPoint = islState.getProgramPoint();
			programPoint_StateMap.put(programPoint, cfgState);
		}
		
		// For each state find out if it's a branch or not.
		// For each state, find out if there is an outgoing branch from that state
		// that transitions to a state which is not in the counter example.
		// if you find such a state, then from that state. run the FINDPATHINCFG() method
		// and find out if that path returns to a state which IS in the counterexample.
		// If you find such a path, then that state is a branching state then you save this information for future use.
		for(int posOfStartState = 0; posOfStartState < counterexample.getLength() - 1; posOfStartState++) {
			// State in consideration at the moment.
			final IPredicate startStateInTrace = counterexample.getStateAtPosition(posOfStartState); 
			// Program point of the state under consideration.final
			final ProgramPoint programpointOfStartStateInTrace = 
					((ISLPredicate) startStateInTrace).getProgramPoint();  
			
			// the startStateInCfg will be forbidden in the alternative path (FORBIDDEN STATE BUG)
			final IPredicate startStateInCfg = programPoint_StateMap.get(programpointOfStartStateInTrace);

			final Set<IPredicate> possibleEndPoints = computePossibleEndpoints(
					counterexample, programPoint_StateMap, posOfStartState);

			final ProgramPoint programPointOfSuccInCounterexample = 
					((ISLPredicate)counterexample.getStateAtPosition(posOfStartState+1)).getProgramPoint();
			//Immediate successors of of the state in CFG
			final Iterable<OutgoingInternalTransition<CodeBlock, IPredicate>> immediateSuccesors = 
					cfg.internalSuccessors(startStateInCfg);
			for(final OutgoingInternalTransition<CodeBlock, IPredicate> transition : immediateSuccesors) {
				final IPredicate immediateSuccesor = transition.getSucc();
				final ProgramPoint programPointOfImmediateSucc = 
						((ISLPredicate)immediateSuccesor).getProgramPoint();
				if (programPointOfImmediateSucc == programPointOfSuccInCounterexample) {
					// do nothing, because we want to find an alternative path
					// (i.e., path that is not in counterexample
				} else {
					 //For Branch in Branch Out information.
					// Path from the successor state not in the counter example 
					// to one of the states in possibleEndPoints.
					final NestedRun<CodeBlock, IPredicate> alternativePath = 
							findPathInCFG(immediateSuccesor,startStateInCfg, possibleEndPoints, cfg);
					if(alternativePath != null) {
						// If such a path exists. Then that means that there is a path from the successor state 
						// that comes back to the counter example
						// THAT MEANS WE HAVE FOUND AN out-BRANCH AT POSITION "COUNTER"
						final IPredicate lastStateOfAlternativePath = 
								alternativePath.getStateAtPosition(alternativePath.getLength()-1);						
						
						final List<Integer> endPosition = computeEndpointOfAlternativePath(
								counterexample, posOfStartState, lastStateOfAlternativePath);
						
						for(final Integer i:endPosition){
							final int[] pair = new int[2];
							//position OUT-BRANCH in the counterexample.
							pair[0] = posOfStartState;
							pair[1] = i-1;
							result_Old.add(pair);
							
							// If the Branch-In Location is not in the map, then add it.
							if(result.get(i-1) == null ){
								final List<Integer> branchInPosArray = new ArrayList<>();
								branchInPosArray.add(posOfStartState);
								result.put(i-1, branchInPosArray);
							} else { 
								//It is in the map, 
								result.get(i-1).add(posOfStartState);
								// The array should be in descending order, so we can delete 
								// the elements from this array more efficiently.
								result.get(i-1).sort(Collections.reverseOrder());
							}							
						}
					}
				}
			}
		}
		return result;
	}

	/**
	 * Returns a List of locations for the occurrence of a state in the Error Trace. 
	 * There can be multiple locations, in case of a loop unrolling.
	 * 
	 * Computing the end point (position of the IN-BRANCH) an alternative path.
	 * Search for the last state in the trace that satisfies
	 * the following properties.
	 * - position in trace is larger than posOfStartState
	 * - program point of the state coincides with 
	 * - program point of lastStateOfAlternativePath
	 *    
	 * Also takes care of the case when for a state in CFG, there are more then one
	 * Occurrences of the corresponding state in the error trace. This can happen, for example,
	 * in the case of a loop un-rolling.
	 */
	private List<Integer> computeEndpointOfAlternativePath(final NestedRun<CodeBlock, IPredicate> counterexample,
			final int posOfStartState, final IPredicate lastStateOfAlternativePath) {
		final List<Integer>  endPoints = new ArrayList<Integer>();
		for(int j = counterexample.getLength() - 1; j > posOfStartState; j--) {
			final IPredicate stateAtPosJ = counterexample.getStateAtPosition(j);
			final ProgramPoint programpointAtPosJ = ((ISLPredicate) stateAtPosJ).getProgramPoint();
			final ProgramPoint programpointOfLastState = ((ISLPredicate)lastStateOfAlternativePath).getProgramPoint();
			if(programpointOfLastState.equals(programpointAtPosJ)) {
				// position of state in the counter example where the branch ends
				endPoints.add(j);
				//return j; 
			}
		}
		if(!endPoints.isEmpty()){
			return endPoints;
		}else {
		throw new AssertionError("endpoint not in trace");
		}
		
	}

	/**
	 * End points are the cfg states (resp. program points) of all successive 
	 * states (successors of currentPosition) in the trace excluding the last 
	 * state (which corresponds to the error location).
	 * @param programPoint_StateMap map from program points to states in cfg
	 */
	private Set<IPredicate> computePossibleEndpoints(final NestedRun<CodeBlock, IPredicate> counterexample,
			final Map<ProgramPoint, IPredicate> programPoint_StateMap, int currentPosition) {
		final Set<IPredicate> possibleEndPoints = new HashSet<IPredicate>();  
		for(int j=currentPosition+1; j< counterexample.getStateSequence().size()-1; j++) {
			//runs only up to size-1 because we do not include the last state (2 Assertion Bug)
			possibleEndPoints.add(programPoint_StateMap.get(((ISLPredicate)counterexample.getStateAtPosition(j)).getProgramPoint()) ); 
		}
		return possibleEndPoints;
	}
	
	
	/**
	 * Computes relevance criterion variables (Unsatisfiable core , Golden Frame).
	 * 
	 * @param relevance
	 */
	private Boolean[] relevanceCriterionVariables(ERelevanceStatus relevance){
		final boolean relevanceCriterionUC;
		final boolean relevanceCriterionGF;
		if(relevance  == ERelevanceStatus.InUnsatCore) {
			// This is the case when the triple is unsatisfiable and the action is in the Unsatisfiable core.
			relevanceCriterionUC = true;
			relevanceCriterionGF = false;
			
		} else if(relevance == ERelevanceStatus.Sat) {
			// The case when we have HAVOC statements. In this case the action is relevant if the triple is satisfiable.
			relevanceCriterionUC = false;
			relevanceCriterionGF = true;
		} else {
			relevanceCriterionUC = false;
			relevanceCriterionGF = false;
		}
		final Boolean[] relevanceCriterionVariables = new Boolean[]{relevanceCriterionUC,relevanceCriterionGF };
		return relevanceCriterionVariables;
	}
	

	
	
	private void doNonFlowSensitiveAnalysis(NestedWord<CodeBlock> counterexampleWord,
		IPredicate falsePredicate, ModifiableGlobalVariableManager modGlobVarManager, SmtManager smtManager) {
		mLogger.info("Starting non-flow-sensitive error relevancy analysis");
		
		final FaultLocalizationRelevanceChecker rc = new FaultLocalizationRelevanceChecker(
				smtManager.getManagedScript(), modGlobVarManager, smtManager.getBoogie2Smt());
		// Non-Flow Sensitive INCREMENTAL ANALYSIS

		// Calculating the WP-List
		final IterativePredicateTransformer ipt = new IterativePredicateTransformer(
				smtManager.getPredicateFactory(), smtManager.getVariableManager(), 
				smtManager.getScript(), smtManager.getBoogie2Smt(), modGlobVarManager, 
				mServices, counterexampleWord, null, falsePredicate, null, 
				smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(falsePredicate)));
		
		final DefaultTransFormulas dtf = new DefaultTransFormulas(counterexampleWord, 
				null, falsePredicate, Collections.emptySortedMap(), modGlobVarManager, false);
		
		
		
		final List<PredicatePostprocessor> postprocessors;
		if (mApplyQuantifierElimination) {
			final QuantifierEliminationPostprocessor qePostproc = 
					new QuantifierEliminationPostprocessor(mServices, mLogger, 
							smtManager.getBoogie2Smt(), smtManager.getPredicateFactory());
			postprocessors = Collections.singletonList(qePostproc);
		} else {
			postprocessors = Collections.emptyList();
		}
		final InterpolantsPreconditionPostcondition weakestPreconditionSequence = 
				ipt.computeWeakestPreconditionSequence(dtf, postprocessors, true);
		// End of the calculation
		
		for(int i = counterexampleWord.length()-1 ; i >= 0; i--) {
				final IAction action = counterexampleWord.getSymbolAt(i);
				// Calculate WP and PRE
				final IPredicate wp = weakestPreconditionSequence.getInterpolant(i+1);
				final IPredicate pre = smtManager.getPredicateFactory().newPredicate(
						smtManager.getPredicateFactory().not(weakestPreconditionSequence.getInterpolant(i)));
				
				// Figure out what is the type of the statement (internal, call or Return)
				final ERelevanceStatus relevance;
				relevance = computeRelevance(i, action, pre, wp, null, weakestPreconditionSequence, 
						counterexampleWord, rc, smtManager);
				

				final Boolean[] relevanceCriterionVariables = relevanceCriterionVariables(relevance);
				final boolean relevanceCriterion1uc = relevanceCriterionVariables[0];
				final boolean relevanceCriterion1gf = relevanceCriterionVariables[1];

				// Adding relevance information in the array list Relevance_of_statements.
				final RelevanceInformation ri = new RelevanceInformation(
						Collections.singletonList(action), 
						relevanceCriterion1uc, 
						relevanceCriterion1gf, ((RelevanceInformation) mRelevanceOfTrace[i]).getCriterion2UC(),
						((RelevanceInformation) mRelevanceOfTrace[i]).getCriterion2GF());
						
				mRelevanceOfTrace[i] = ri;
		}
		
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("- - - - - - [Non-Flow Sensitive Analysis with statments + pre/wp information]- - - - - -");
			for (int i=0; i<counterexampleWord.length(); i++) {
				mLogger.debug(weakestPreconditionSequence.getInterpolant(i));
				mLogger.debug(mRelevanceOfTrace[i]);
			}
			mLogger.debug(weakestPreconditionSequence.getInterpolant(counterexampleWord.length()));
			mLogger.debug("------------------------------------------------------------------------------------------");
		}
	}
	
	
	/**
	 * Recursively Compute the Markhor Formula of a branch.
	 * @param startPosition - Starting location of the branch.
	 * @param endPosition -  End location of the branch.
	 */
	private TransFormula computeMarkhorFormula(int startPosition, int endPosition, 
			NestedWord<CodeBlock> counterexampleWord, Map<Integer, List<Integer>> informationFromCFG, 
			SmtManager smtManager){
		TransFormula combinedTransitionFormula = counterexampleWord.getSymbolAt(startPosition).getTransitionFormula();
		for(int i = startPosition+1; i<= endPosition; i++){
			boolean subBranch=false;
			int branchOut=0;
			int branchIn=0;
			//Find out if the current position is a branchOut position.
			for(final Integer brachInPosition:informationFromCFG.keySet()){
				if(informationFromCFG.get(brachInPosition).contains(i)){
					subBranch = true;
					branchOut = i;
					branchIn = brachInPosition -1;
					i = branchIn;
					break;
				}
			}
			if(subBranch){
				 // The current statement is a branch out and it's branch-in is with in the current branch.
				final TransFormula subBranchMarkhorFormula = computeMarkhorFormula(branchOut,branchIn,counterexampleWord,
						informationFromCFG,smtManager);
				combinedTransitionFormula = TransFormula.sequentialComposition(mLogger, mServices, 
						smtManager.getBoogie2Smt(), false, false, false, combinedTransitionFormula,subBranchMarkhorFormula);
			} else{ 
				// It is a normal statement.
				final CodeBlock statement = counterexampleWord.getSymbol(i);
				final TransFormula transitionFormula = statement.getTransitionFormula();
				combinedTransitionFormula = TransFormula.sequentialComposition(mLogger, mServices, 
						smtManager.getBoogie2Smt(), false, false, false, combinedTransitionFormula,transitionFormula);
			}
		}
		final TransFormula markhor = TransFormula.computeMarkhorTransFormula(combinedTransitionFormula, 
				smtManager.getBoogie2Smt(), mServices, mLogger);
		return markhor;
	}
	
	/**
	 * Checks if subtrace from position "startPosition" to position "endPosition" is relevant.
	 */
	private boolean checkBranchRelevance(int startPosition, int endPosition, 
			TransFormula markhor,IPredicate weakestPreconditionLeft, 
			IPredicate weakestPreconditionRight, NestedWord<CodeBlock> counterexampleWord, 
			SmtManager smtManager, ModifiableGlobalVariableManager modGlobVarManager){

		final FaultLocalizationRelevanceChecker rc = new FaultLocalizationRelevanceChecker(
				smtManager.getManagedScript(), modGlobVarManager, smtManager.getBoogie2Smt());
		final IPredicate pre = smtManager.getPredicateFactory().newPredicate(
				smtManager.getPredicateFactory().not(weakestPreconditionLeft));
		final String preceeding = counterexampleWord.getSymbolAt(startPosition).getPreceedingProcedure();
		final String succeeding = counterexampleWord.getSymbolAt(endPosition).getSucceedingProcedure();
		final BasicInternalAction basic = new BasicInternalAction(preceeding, succeeding, markhor);
		final ERelevanceStatus relevance = rc.relevanceInternal(pre, basic, 
				smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(weakestPreconditionRight)));
		if(relevance == ERelevanceStatus.InUnsatCore || relevance == ERelevanceStatus.Sat){ 
			// Branch is RELEVANT
			return true;	
		}else{ 
			// BRANCH IS NOT RELEVANT
			return false; 
		}
	}

	
	/**
	 * Computes the corresponding branch-out position for a given branch-in 
	 * position. 
	 * @param branchInList branch-in positions in descending order 
	 * @return the smallest element of the branchInList that is larger than 
	 * startLocation. Returns null if no such element exists.
	 */
	private Integer computeCorrespondingBranchOutLocation(
			final List<Integer> branchInList, final int startLocation) {
		assert (branchInList != null && !branchInList.isEmpty());
		for(int i=branchInList.size()-1; i>=0; i--) {
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
	private void computeRelevantStatements_FlowSensitive(final NestedWord<CodeBlock> counterexampleWord,
			final int startLocation, final int endLocation, final IPredicate weakestPreconditionBranchEndlocation,
			final PredicateTransformer pt, final FaultLocalizationRelevanceChecker rc, 
			final SmtManager smtManager, final ModifiableGlobalVariableManager modGlobVarManager, 
			final Map<Integer, List<Integer>> informationFromCFG) {
		IPredicate weakestPreconditionLeft = weakestPreconditionBranchEndlocation;
		for (int position = endLocation; position >= startLocation; position--){
			final CodeBlock statement = counterexampleWord.getSymbol(position);

			final List<Integer> branchIn = informationFromCFG.get(position);
			final Integer branchOutPosition;
			if (branchIn != null && !branchIn.isEmpty()) {
				// Branch IN Statement
				 branchOutPosition = computeCorrespondingBranchOutLocation(
					branchIn, startLocation);
			} else {
				branchOutPosition = null;
			}
			final IPredicate weakestPreconditionRight = weakestPreconditionLeft;
			if (branchOutPosition != null) {
				final int positionBranchIn = position;
				position = branchOutPosition;
				final TransFormula markhor = computeMarkhorFormula(branchOutPosition, positionBranchIn, 
						counterexampleWord,informationFromCFG, smtManager);
				final Term wpTerm = computeWp(weakestPreconditionRight, markhor, smtManager.getScript(), 
						smtManager.getVariableManager(), pt, mApplyQuantifierElimination);
				weakestPreconditionLeft = smtManager.getPredicateFactory().newPredicate(wpTerm);
				// Check the relevance of the branch.
				final boolean isRelevant =  checkBranchRelevance(
						branchOutPosition,positionBranchIn,markhor,weakestPreconditionLeft, 
						weakestPreconditionRight,counterexampleWord,
						smtManager,modGlobVarManager);
				if(isRelevant){ 
					// If the branch is Relevant. Recursion
					computeRelevantStatements_FlowSensitive(
							counterexampleWord, branchOutPosition,positionBranchIn,
							weakestPreconditionRight,pt,rc,smtManager,modGlobVarManager,informationFromCFG);
				} else{
					// Don't do anything.
					mLogger.debug(" - - Irrelevant Branch - - - [MarkhorFormula:"+ markhor + " ]");
				}

			} else { 
				// The statement under consideration is NOT a BRANCH-IN Statement.
				
				final TransFormula tf =  counterexampleWord.getSymbolAt(position).getTransitionFormula();
				final Term wpTerm = computeWp(weakestPreconditionRight, tf, smtManager.getScript(), 
						smtManager.getVariableManager(), pt, mApplyQuantifierElimination);
				weakestPreconditionLeft = smtManager.getPredicateFactory().newPredicate(wpTerm);
				final IPredicate pre = smtManager.getPredicateFactory().newPredicate(
						smtManager.getPredicateFactory().not(weakestPreconditionLeft));
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(" ");
					mLogger.debug("WP -- > " + weakestPreconditionRight);
					mLogger.debug(" Statement -- > " + statement);
					mLogger.debug("Pre --> " +  pre);
					mLogger.debug(" " );
				}
				final IAction action = counterexampleWord.getSymbolAt(position);
				final ERelevanceStatus relevance = computeRelevance(position,action,pre,weakestPreconditionRight,
						weakestPreconditionLeft,null,counterexampleWord,
						rc,smtManager);
				final Boolean[] relevanceCriterionVariables = relevanceCriterionVariables(relevance);
				final boolean relevanceCriterion2uc = relevanceCriterionVariables[0];
				final boolean relevanceCriterion2gf = relevanceCriterionVariables[1];
				final RelevanceInformation ri = new RelevanceInformation(
						Collections.singletonList(action), 
						((RelevanceInformation) mRelevanceOfTrace[position]).getCriterion1UC(), 
						((RelevanceInformation) mRelevanceOfTrace[position]).getCriterion1GF(), 
						relevanceCriterion2uc, relevanceCriterion2gf);
				mRelevanceOfTrace[position] = ri;
			}
		}
	}
	
	/**
	 * Computes the relevance information of a position in the trace, depending on the
	 * type of the codeblock at that location. (IInternalAction, ICallAction, IReturnAction).
	 * 
	 * @return Relevance Information of a position in the trace.
	 */
	private ERelevanceStatus computeRelevance(int position, IAction action, IPredicate pre, 
			IPredicate weakestPreconditionRight, IPredicate weakestPreconditionLeft, 
			InterpolantsPreconditionPostcondition weakestPreconditionSequence, 
			NestedWord<CodeBlock> counterexampleWord, 
			FaultLocalizationRelevanceChecker rc, SmtManager smtManager){
		ERelevanceStatus relevance;
		if(action instanceof IInternalAction){
			final IInternalAction internal = (IInternalAction) counterexampleWord.getSymbolAt(position);
			relevance = rc.relevanceInternal(pre, internal, 
					smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(weakestPreconditionRight)));
		}else if(action instanceof ICallAction){
			final ICallAction call = (ICallAction) counterexampleWord.getSymbolAt(position);
			relevance = rc.relevanceCall(pre, call, 
					smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(weakestPreconditionRight)));
		}else if(action instanceof IReturnAction){
			final IReturnAction ret = (IReturnAction) counterexampleWord.getSymbolAt(position);
			assert counterexampleWord.isReturnPosition(position);
			assert !counterexampleWord.isPendingReturn(position) : "pending returns not supported";
			final IPredicate callPredecessor;
			if(weakestPreconditionSequence != null) { 
				// In case of Non-FlowSensitive
				final int callPos = counterexampleWord.getCallPosition(position);
				callPredecessor = weakestPreconditionSequence.getInterpolant(callPos); 
			} else{ 
				//In case of FlowSensitive.
				callPredecessor = weakestPreconditionLeft; 
			}
			
			relevance = rc.relevanceReturn(pre, callPredecessor, ret, 
					smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(weakestPreconditionRight)));
		} else{
			throw new AssertionError("Unknown Action " +
					action.getClass().getSimpleName());
		}
		return relevance;		
	}
	
	

	/**
	 * Compute WP and optionally apply quantifier elimination. 
	 */
	private Term computeWp(IPredicate successor, TransFormula tf, Script script, 
			IFreshTermVariableConstructor freshTermVariableConstructor, 
			PredicateTransformer pt, boolean applyQuantifierElimination) {
		Term result = pt.weakestPrecondition(successor, tf);
		if (applyQuantifierElimination) {
			result = PartialQuantifierElimination.tryToEliminate(mServices, 
					mLogger, script, freshTermVariableConstructor, result);
		}
		return result;
	}
	
	private void doFlowSensitiveAnalysis(NestedRun<CodeBlock, IPredicate> counterexample,
			INestedWordAutomaton<CodeBlock, IPredicate> cfg,
			ModifiableGlobalVariableManager modGlobVarManager, 
			SmtManager smtManager){
		mLogger.info("Starting flow-sensitive error relevancy analysis");
		final Map<Integer, List<Integer>> informationFromCFG = computeInformationFromCFG(counterexample, cfg); 
		// You should send the counter example, the CFG information and the the start of the branch and the end of the branch.
		final PredicateTransformer pt = new PredicateTransformer(smtManager.getVariableManager(), 
				smtManager.getScript(), modGlobVarManager, mServices);
		final FaultLocalizationRelevanceChecker rc = new FaultLocalizationRelevanceChecker(
				smtManager.getManagedScript(), modGlobVarManager, smtManager.getBoogie2Smt());
		final int startLocation = 0;
		final int endLocation = counterexample.getWord().length()-1;
		final IPredicate falsePredicate = smtManager.getPredicateFactory().newPredicate(
				smtManager.getScript().term("false"));

		computeRelevantStatements_FlowSensitive(counterexample.getWord(),startLocation, endLocation,
				falsePredicate, pt, rc, smtManager,modGlobVarManager, informationFromCFG);


	}



	/**
	 * Check if there is a path from startPoint so some element of the 
	 * possibleEndPoints set.
	 * If yes, a NestedRun is returned, otherwise null is returned.
	 * @param parent_state 
	 * 
	 * @throws ToolchainCanceledException if toolchain was cancelled (e.g., 
	 * because of a timeout)
	 */
	private NestedRun<CodeBlock, IPredicate> findPathInCFG(IPredicate startPoint, 
			IPredicate parent_state, Set<IPredicate> possibleEndPoints, INestedWordAutomaton<CodeBlock, 
			IPredicate> cfg) {
		try {
			return (new IsEmpty<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices), cfg, 
					Collections.singleton(startPoint), Collections.singleton(parent_state), possibleEndPoints)).getNestedRun();
		} catch (final AutomataOperationCanceledException e) {
			throw new ToolchainCanceledException(getClass());
		}
	}
	
	/**
	 * @return List of {@link RelevanceInformation}s one for each 
	 * {@link CodeBlock} in the counterexample.
	 */
	public List<IRelevanceInformation> getRelevanceInformation() {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("- - - - - - - -");
			for(int i= 0; i <mRelevanceOfTrace.length; i++) {
				mLogger.debug(((RelevanceInformation) mRelevanceOfTrace[i]).getActions() + 
						" | " +mRelevanceOfTrace[i].getShortString());
			}
		}
		return Arrays.asList(mRelevanceOfTrace);
	}
	
	
}
