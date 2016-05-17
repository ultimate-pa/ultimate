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
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.ILogger;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
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
import de.uni_freiburg.informatik.ultimate.result.model.IRelevanceInformation;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;
/**
 * 
 * @author Numair Mansur
 * @author Matthias Heizmann
 * @author Christian Schilling
 * 
 *
 */
public class FlowSensitiveFaultLocalizer {

	private final IUltimateServiceProvider m_Services;
	private final ILogger m_Logger;
	private final IRelevanceInformation[] m_RelevanceOfTrace;
	/**
	 * Apply quantifier elimination during the computation of pre and wp.
	 * If set to true, there is a higher risk that we run into a timeout.
	 * If set to false, there is a higher risk that the SMT solver returns 
	 * unknown.
	 */
	private final boolean m_ApplyQuantifierElimination = true;

	public FlowSensitiveFaultLocalizer(IRun<CodeBlock, IPredicate> counterexample,
			INestedWordAutomaton<CodeBlock, IPredicate> cfg, IUltimateServiceProvider services,
			SmtManager smtManager,
			ModifiableGlobalVariableManager modGlobVarManager, PredicateUnifier predicateUnifier) {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		m_RelevanceOfTrace = initializeRelevanceOfTrace(counterexample);
		final Map<Integer, List<Integer>> informationFromCFG = computeInformationFromCFG(
				(NestedRun<CodeBlock, IPredicate>) counterexample, cfg); 
		computeNONFlowSensitiveTraceFormula((NestedWord<CodeBlock>) counterexample.getWord(),
				predicateUnifier.getFalsePredicate(), modGlobVarManager, smtManager);
		computeFlowSensitiveTraceFormula((NestedWord<CodeBlock>) counterexample.getWord(),
				predicateUnifier.getFalsePredicate(), modGlobVarManager, smtManager,informationFromCFG);
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
	private Map<Integer, List<Integer>> computeInformationFromCFG(final NestedRun<CodeBlock, IPredicate> counterexample,
			final INestedWordAutomaton<CodeBlock, IPredicate> cfg){
		final List<int[]> result = new ArrayList<>();
		
		//Using Better Data Structure to save graph information. 
		final Map<Integer, List<Integer>> result2 = new HashMap<Integer, List<Integer>>();

		
		// Create a Map of Program_points in the CFG to States of the CFG.
		final Map <ProgramPoint,IPredicate> programPoint_StateMap = new HashMap<>();
		for (IPredicate cfgState : cfg.getStates()) {
			final ISLPredicate islState  = (ISLPredicate) cfgState;
			final ProgramPoint program_point = islState.getProgramPoint();
			programPoint_StateMap.put(program_point, cfgState);
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
			for(OutgoingInternalTransition<CodeBlock, IPredicate> transition : immediateSuccesors) {
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
						
						for(Integer i:endPosition){
							final int[] pair = new int[2];
							pair[0] = posOfStartState; //position OUT-BRANCH in the counterexample.
							pair[1] = i;
							result.add(pair);
							
							// If the Branch-In Location is not in the map, then add it.
							if(result2.get(i) == null ){
								final List<Integer> branchInPosArray = new ArrayList<>();
								branchInPosArray.add(posOfStartState);
								result2.put(i, branchInPosArray);
							} else{ //It is in the map, 
								result2.get(i).add(posOfStartState);
								// The array should be in descending order, so we can delete 
								// the elements from this array more efficiently.
								result2.get(i).sort(Collections.reverseOrder());
							}
							
							
							
						}

						

						
					}
				}
			}
		}
		return result2;
	}

	/**
	 * Computing the end point (position of the IN-BRANCH) an alternative path.
	 * Search for the last state in the trace that satisfies
	 * the following properties.
	 * - position in trace is larger than posOfStartState
	 * - program point of the state coincides with 
	 *    program point of lastStateOfAlternativePath
	 */
	private List<Integer> computeEndpointOfAlternativePath(final NestedRun<CodeBlock, IPredicate> counterexample,
			final int posOfStartState, final IPredicate lastStateOfAlternativePath) {
		List<Integer>  endPoints = new ArrayList<Integer>();
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
		if(endPoints.size() != 0){
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
		Boolean[] relevanceCriterionVariables = new Boolean[]{relevanceCriterionUC,relevanceCriterionGF };
		return relevanceCriterionVariables;
	}
	

	
	
	private void computeNONFlowSensitiveTraceFormula(NestedWord<CodeBlock> counterexampleWord,
		IPredicate falsePredicate, ModifiableGlobalVariableManager modGlobVarManager, SmtManager smtManager) {
		
		final FaultLocalizationRelevanceChecker rc = new FaultLocalizationRelevanceChecker(
				smtManager.getManagedScript(), modGlobVarManager, smtManager.getBoogie2Smt());
		// Non-Flow Sensitive INCREMENTAL ANALYSIS

		// Calculating the WP-List
		final IterativePredicateTransformer ipt = new IterativePredicateTransformer(
				smtManager.getPredicateFactory(), smtManager.getVariableManager(), 
				smtManager.getScript(), smtManager.getBoogie2Smt(), modGlobVarManager, 
				m_Services, counterexampleWord, null, falsePredicate, null, 
				smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(falsePredicate)));
		
		final DefaultTransFormulas dtf = new DefaultTransFormulas(counterexampleWord, 
				null, falsePredicate, Collections.emptySortedMap(), modGlobVarManager, false);
		
		
		
		final List<PredicatePostprocessor> postprocessors;
		if (m_ApplyQuantifierElimination) {
			final QuantifierEliminationPostprocessor qePostproc = 
					new QuantifierEliminationPostprocessor(m_Services, m_Logger, 
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
				if(action instanceof IInternalAction) {
					IInternalAction internal = (IInternalAction) counterexampleWord.getSymbolAt(i);
					relevance = rc.relevanceInternal(pre, internal, 
							smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(wp)));
				} else if(action instanceof ICallAction) {
					ICallAction call = (ICallAction) counterexampleWord.getSymbolAt(i);
					relevance = rc.relevanceCall(pre, call, 
							smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(wp)));
				} else if(action instanceof IReturnAction) {
					IReturnAction ret = (IReturnAction) counterexampleWord.getSymbolAt(i);
					assert counterexampleWord.isReturnPosition(i);
					assert !counterexampleWord.isPendingReturn(i) : "pending returns not supported";
					final int callPos = counterexampleWord.getCallPosition(i);
					final IPredicate callPredecessor = weakestPreconditionSequence.getInterpolant(callPos); 
					relevance = rc.relevanceReturn(pre, callPredecessor, 
							ret, smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(wp)));
				} else {
					throw new IllegalArgumentException("Unknown Action " +
							action.getClass().getSimpleName());
				}
				

				Boolean[] relevanceCriterionVariables = relevanceCriterionVariables(relevance);
				final boolean relevanceCriterion1uc = relevanceCriterionVariables[0];
				final boolean relevanceCriterion1gf = relevanceCriterionVariables[1];

				// Adding relevance information in the array list Relevance_of_statements.
				final RelevanceInformation ri = new RelevanceInformation(
						Collections.singletonList(action), 
						relevanceCriterion1uc, 
						relevanceCriterion1gf, ((RelevanceInformation) m_RelevanceOfTrace[i]).getCriterion2UC(),
						((RelevanceInformation) m_RelevanceOfTrace[i]).getCriterion2GF());
						
				m_RelevanceOfTrace[i] = ri;
		}
		
		m_Logger.info("- - - - - - [Non-Flow Sensitive Analysis with statments + pre/wp information]- - - - - -");
		if (m_Logger.isInfoEnabled()) {
			for (int i=0; i<counterexampleWord.length(); i++) {
				m_Logger.info(weakestPreconditionSequence.getInterpolant(i));
				m_Logger.info(m_RelevanceOfTrace[i]);
			}
			m_Logger.info(weakestPreconditionSequence.getInterpolant(counterexampleWord.length()));
		}
		m_Logger.info("------------------------------------------------------------------------------------------");

		
	}
	
	
	/**
	 * Recursively Compute the Markhor Formula of a branch.
	 * @param a Starting location of the branch.
	 * @param b End location of the branch.
	 * @param counterexampleWord 
	 * @param informationFromCFG
	 * @param smtManager
	 * @return
	 */
	private TransFormula computeMarkhorFormula(int a, int b, NestedWord<CodeBlock> counterexampleWord, Map<Integer, List<Integer>> informationFromCFG, SmtManager smtManager){
		TransFormula combinedTransitionFormula = counterexampleWord.getSymbolAt(a).getTransitionFormula();
		for(int i = a+1; i<=b; i++){
			boolean subBranch=false;
			int branchOut = 0;
			int branchIn = 0;
			
			
			for(Integer brachInPosition:informationFromCFG.keySet()){
				if(informationFromCFG.get(brachInPosition).contains(i)){
					subBranch = true;
					branchOut = i;
					branchIn = brachInPosition -1;
					i = branchIn;
				}
			}
			
			if(subBranch){ // The current statement is a branch out and it's branch-in is with in the current branch. 
				TransFormula sub_markhor = computeMarkhorFormula(branchOut,branchIn,counterexampleWord,informationFromCFG,smtManager);
				combinedTransitionFormula = TransFormula.sequentialComposition(m_Logger, m_Services, smtManager.getBoogie2Smt(), false, false, false, combinedTransitionFormula,sub_markhor);
			}
			else{ // It is a normal statement.
				final CodeBlock Statement = counterexampleWord.getSymbol(i);
				final TransFormula TransitionFormula = Statement.getTransitionFormula();
				combinedTransitionFormula = TransFormula.sequentialComposition(m_Logger, m_Services, smtManager.getBoogie2Smt(), false, false, false, combinedTransitionFormula,TransitionFormula);
			}
		}
		final TransFormula markhor = TransFormula.computeMarkhorTransFormula(combinedTransitionFormula, smtManager.getBoogie2Smt(), m_Services, m_Logger);
		return markhor;
	}
	
	/**
	 * Checks if subtrace from position a to position b is relevant.
	 * 
	 * @param a
	 * @param b
	 * @param weakestPreconditionOld
	 * @param counterexampleWord
	 * @param informationFromCFG
	 * @param smtManager
	 * @param modGlobVarManager
	 * @return
	 */
	private TransFormula[] checkBranchRelevance(int a, int b, IPredicate weakestPreconditionOld, NestedWord<CodeBlock> counterexampleWord, 
			Map<Integer, List<Integer>> informationFromCFG, SmtManager smtManager, ModifiableGlobalVariableManager modGlobVarManager){
		
		
		final PredicateTransformer pt = new PredicateTransformer(smtManager.getVariableManager(), 
				smtManager.getScript(), modGlobVarManager, m_Services);
		final FaultLocalizationRelevanceChecker rc = new FaultLocalizationRelevanceChecker(smtManager.getManagedScript(), modGlobVarManager, smtManager.getBoogie2Smt());
		final TransFormula markhor = computeMarkhorFormula(a, b, counterexampleWord,informationFromCFG, smtManager);
		final Term wpTerm = computeWp(weakestPreconditionOld, markhor, smtManager.getScript(), 
				smtManager.getVariableManager(), pt, m_ApplyQuantifierElimination);
		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(wpTerm, smtManager.getBoogie2Smt());
		final IPredicate weakestPreconditionNew = smtManager.getPredicateFactory().newPredicate(tvp);
		final IPredicate pre = smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(weakestPreconditionNew));
		final String preceeding = counterexampleWord.getSymbolAt(a).getPreceedingProcedure();
		final String succeeding = counterexampleWord.getSymbolAt(b).getSucceedingProcedure();
		final BasicInternalAction basic = new BasicInternalAction(preceeding, succeeding, markhor);

		final ERelevanceStatus relevance = rc.relevanceInternal(pre, basic, smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(weakestPreconditionOld)));
		if(relevance == ERelevanceStatus.InUnsatCore || relevance == ERelevanceStatus.Sat){ // Branch is RELEVANT
			return new TransFormula[]{markhor,markhor};
			
			
		}
		else{ // BRANCH IS NOT RELEVANT
			return new TransFormula[]{markhor,null}; // IF the second value is null, the branch is NOT relevant.
		}
	}

/**
 * Computes the Statements relevant to the flow sensitive analysis in the trace. 
 * @return  A list of relevant statements. The main contribution of this method is update of RelevancyCriterion variables
 * 			in the RelevanceInformation Objects.
 */
	private ArrayList<CodeBlock> relevantFlowSensitiveStatements(NestedWord<CodeBlock> counterexampleWord,
			int start_location, int end_location, IPredicate weakestPreconditionOld, IPredicate weakestPreconditionNew,
			PredicateTransformer pt, FaultLocalizationRelevanceChecker rc, SmtManager smtManager,
			ModifiableGlobalVariableManager modGlobVarManager, Map<Integer, List<Integer>> informationFromCFG) {
		ArrayList <CodeBlock> relevantStatements = new ArrayList<CodeBlock>();
		IPredicate pre = null;
		ERelevanceStatus relevance;
		for (int position = end_location; position >= start_location; position--){
			final CodeBlock Statement = counterexampleWord.getSymbol(position);
			boolean isBranchIn = false;
			int positionBranchOut = 0;
			int positionBranchIn = 0;
			// Find out if the current Statement is a BRANCH-IN statement.
			List<Integer> branchIn = informationFromCFG.get(position+1);
			if(branchIn != null && branchIn.size() > 0){ // null is not enough, the list can also be empty, hence 2 conditions.
				// We are on a branch-in Statement'
				int sizeOfbranchInPosArray = branchIn.size();
				positionBranchOut = branchIn.get(sizeOfbranchInPosArray-1); //fetch the last element.
				positionBranchIn = position;
				informationFromCFG.get(position+1).remove(sizeOfbranchInPosArray-1);
				position = positionBranchOut;
				isBranchIn = true;
				
			}
			
			if(isBranchIn){ // The current statement is a BRANCH-IN Statement.
				
				// Check the relevance of the branch ?
				final TransFormula[] markhor_formula =  checkBranchRelevance(
						positionBranchOut,positionBranchIn,weakestPreconditionNew,counterexampleWord,
						informationFromCFG,smtManager,modGlobVarManager);
				if(markhor_formula[1] != null){ // If the branch is Relevant.
					//Recursion
					ArrayList<CodeBlock> relevantSubStatements = relevantFlowSensitiveStatements(
							counterexampleWord, positionBranchOut,positionBranchIn,weakestPreconditionNew,
							weakestPreconditionNew,pt,rc,smtManager,modGlobVarManager,informationFromCFG);
					relevantStatements.addAll(relevantSubStatements);
				}
				else{

					m_Logger.info(" - - Irrelevant Branch - - - [MarkhorFormula:"+ markhor_formula + " ]");
				}
				final Term wpTerm = computeWp(weakestPreconditionNew, markhor_formula[0], smtManager.getScript(), 
						smtManager.getVariableManager(), pt, m_ApplyQuantifierElimination);
				final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(wpTerm, smtManager.getBoogie2Smt());
				weakestPreconditionNew = smtManager.getPredicateFactory().newPredicate(tvp);
				// If the branch is relevant, then recursively call the same function on it self with the updated parameters.
				// If the branch is not relevant, then just ignore the branch and update the backward counter and also take a look what should you do with the pre and wp.
				

			}
			else{ // The statement under consideration is NOT a BRANCH-IN Statement.
				weakestPreconditionOld = weakestPreconditionNew;
				final TransFormula tf =  counterexampleWord.getSymbolAt(position).getTransitionFormula();
				final Term wpTerm = computeWp(weakestPreconditionOld, tf, smtManager.getScript(), 
						smtManager.getVariableManager(), pt, m_ApplyQuantifierElimination);
				final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(wpTerm, smtManager.getBoogie2Smt());
				weakestPreconditionNew = smtManager.getPredicateFactory().newPredicate(tvp);
				pre = smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(weakestPreconditionNew));
				m_Logger.info(" ");
				m_Logger.info("WP -- > " + weakestPreconditionOld);
				m_Logger.info(" Statement -- > " + Statement);
				m_Logger.info("Pre --> " +  pre);
				m_Logger.info(" " );
				final IAction action = counterexampleWord.getSymbolAt(position);
				if(action instanceof IInternalAction)
				{
					final IInternalAction internal = (IInternalAction) counterexampleWord.getSymbolAt(position);
					relevance = rc.relevanceInternal(pre, internal, smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(weakestPreconditionOld)));
				}
				else if(action instanceof ICallAction){
					ICallAction call = (ICallAction) counterexampleWord.getSymbolAt(position);
					relevance = rc.relevanceCall(pre, call, smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(weakestPreconditionOld)));
				}
				else if(action instanceof IReturnAction){
					IReturnAction returnn = (IReturnAction) counterexampleWord.getSymbolAt(position);
					assert counterexampleWord.isReturnPosition(position);
					assert !counterexampleWord.isPendingReturn(position) : "pending returns not supported";
					final IPredicate callPredecessor = weakestPreconditionNew; 
					relevance = rc.relevanceReturn(pre, callPredecessor, returnn, smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(weakestPreconditionOld)));
				}
				else{
					throw new AssertionError("Unknown Action " +
							action.getClass().getSimpleName());
				}
				
				
				Boolean[] relevanceCriterionVariables = relevanceCriterionVariables(relevance);
				final boolean relevanceCriterion2uc = relevanceCriterionVariables[0];
				final boolean relevanceCriterion2gf = relevanceCriterionVariables[1];
				
				RelevanceInformation ri = new RelevanceInformation(
						Collections.singletonList(action), 
						((RelevanceInformation) m_RelevanceOfTrace[position]).getCriterion1UC() , 
						((RelevanceInformation) m_RelevanceOfTrace[position]).getCriterion1GF(), relevanceCriterion2uc, relevanceCriterion2gf);
						
				m_RelevanceOfTrace[position] = ri;
				
			}

			
		}
		
		return(relevantStatements);
	
	}

	/**
	 * Compute WP and optionally apply quantifier elimination. 
	 */
	private Term computeWp(IPredicate successor, TransFormula tf, Script script, 
			IFreshTermVariableConstructor freshTermVariableConstructor, 
			PredicateTransformer pt, boolean applyQuantifierElimination) {
		Term result = pt.weakestPrecondition(successor, tf);
		if (applyQuantifierElimination) {
			result = PartialQuantifierElimination.tryToEliminate(m_Services, 
					m_Logger, script, freshTermVariableConstructor, result);
		}
		return result;
	}
	
	private void computeFlowSensitiveTraceFormula(NestedWord<CodeBlock> counterexampleWord,
			IPredicate falsePredicate, ModifiableGlobalVariableManager modGlobVarManager, SmtManager smtManager, 
			Map<Integer, List<Integer>> informationFromCFG ){


		m_Logger.info("Initializing Flow Sensitive Fault Localization");
		// You should send the counter example, the CFG information and the the start of the branch and the end of the branch.
		PredicateTransformer pt = new PredicateTransformer(smtManager.getVariableManager(), smtManager.getScript(), modGlobVarManager, m_Services);
		FaultLocalizationRelevanceChecker rc = new FaultLocalizationRelevanceChecker(smtManager.getManagedScript(), modGlobVarManager, smtManager.getBoogie2Smt());
		int start_location = 0;
		int end_location = counterexampleWord.length()-1;
		IPredicate weakestPreconditionOld = smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().constructFalse());
		IPredicate weakestPreconditionNew = weakestPreconditionOld;

		relevantFlowSensitiveStatements(counterexampleWord,start_location, end_location,weakestPreconditionOld,
				weakestPreconditionNew, pt, rc, smtManager,modGlobVarManager, informationFromCFG);


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
			IPredicate> cfg) 
	{

		
		try 
		{
			return (new IsEmpty<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services), cfg, 
					Collections.singleton(startPoint), Collections.singleton(parent_state), possibleEndPoints)).getNestedRun();
		} 
		
		catch (OperationCanceledException e) 
		{
			throw new ToolchainCanceledException(getClass());
		}
	}
	
	/**
	 * @return List of {@link RelevanceInformation}s one for each 
	 * {@link CodeBlock} in the counterexample.
	 */
	public List<IRelevanceInformation> getRelevanceInformation() 
	{
		m_Logger.warn("- - - - - - - -");
		for(int i= 0;i <m_RelevanceOfTrace.length;i++)
		{
			m_Logger.warn(((RelevanceInformation) m_RelevanceOfTrace[i]).getActions() +" | " +m_RelevanceOfTrace[i].getShortString());
		}
		return Arrays.asList(m_RelevanceOfTrace);
	}
	
}
