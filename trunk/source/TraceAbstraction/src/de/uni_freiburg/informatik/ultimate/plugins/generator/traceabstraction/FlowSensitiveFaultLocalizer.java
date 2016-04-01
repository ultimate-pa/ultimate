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
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.WalkerOptions.State;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Cnf;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.FaultLocalizationRelevanceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.FaultLocalizationRelevanceChecker.ERelevanceStatus;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.DefaultTransFormulas;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.NestedFormulas;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.NestedSsaBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;
import de.uni_freiburg.informatik.ultimate.result.IRelevanceInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.RelevanceInformation;
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

	private IUltimateServiceProvider m_Services;
	private final Logger m_Logger;
	private ArrayList<IRelevanceInformation> Relevance_of_statements = new ArrayList<>(); 

	public FlowSensitiveFaultLocalizer(IRun<CodeBlock, IPredicate> counterexample,
			INestedWordAutomaton<CodeBlock, IPredicate> cfg, IUltimateServiceProvider services, SmtManager smtManager,
			ModifiableGlobalVariableManager modGlobVarManager, PredicateUnifier predicateUnifier) {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		ArrayList<int[]> informationFromCFG = computeInformationFromCFG( (NestedRun<CodeBlock, IPredicate>) counterexample, cfg); //Get branch information. in the form of an array list
		computeFlowSensitiveTraceFormula(counterexample, predicateUnifier.getFalsePredicate(), modGlobVarManager, smtManager,informationFromCFG);
	}


	private ArrayList<int[]> computeInformationFromCFG(NestedRun<CodeBlock, IPredicate> counterexample,
			INestedWordAutomaton<CodeBlock, IPredicate> cfg) 
	{
		m_Logger.warn("Computing Graph Information . . . . ");
		ArrayList<int[]> result = new ArrayList<>();
		int size = counterexample.getStateSequence().size();
		IPredicate start_state = null;
		// For each state find out if it's a branch or not.
		// For each state, find out if there is an outgoing branch from that state
		// that transitions to a state which is not in the counter example.
		// if you find such a state, then from that state. run the FINDPATHINCFG() method
		// and find out if that path returns to a state which IS in the counterexample.
		// If you find such a path, then that state is a branching state then you save this information for future use.
		//  **** REMEMBER THE CASE WHEN THERE ARE TWO OUTGOING BRANCHES FROM A STATE GOING IN THE SAME BRANCH ****
		for(int counter = 0; counter < counterexample.getLength();counter++) // For all States
		{
			start_state = counterexample.getStateAtPosition(counter); // State in consideration at the moment
			Iterable<OutgoingInternalTransition<CodeBlock, IPredicate>> succesors = cfg.internalSuccessors(start_state); //Immediate successors of of the state in CFG
			Set<IPredicate> possibleEndPoints =  new HashSet<IPredicate>();  // all the successive states of the current state in the counter example
			for(int j=counter+1; j< size; j++)
			{
				possibleEndPoints.add((IPredicate) counterexample.getStateAtPosition(j)); // Pushing all the successive states from the counter example
			}
			for( OutgoingInternalTransition<CodeBlock, IPredicate> test:succesors) // For all the immediate successor states of the state in focus
			{
				IPredicate succesor2 = test.getSucc(); // One of the successors of the the state in focus.
				if(succesor2 != counterexample.getStateAtPosition(counter+1)) // If this successor state is NOT the next state of the current state in the counter example
				{	
					int[] tuple = new int[2]; // Initialize tuple
					//m_Logger.warn("Found a state not in the counter example -->>" + succesor2);
					NestedRun<CodeBlock, IPredicate> path = findPathInCFG(succesor2, possibleEndPoints, cfg); // Path from the successor state not in the counter example till one of the states in the possible end points.
					//m_Logger.warn("Path -->  "+ path);
					if(path != null) // If such a path exists. Then that means that there is a path from the successor state that comes back to the counter example
					{ // THAT MEANS WE HAVE FOUND AN IF BRANCH AT POSITION "COUNTER" !!
						// Found an IF branch at position 1 of the counter example.
						int length = path.getLength();
						IPredicate last_state_of_the_path = path.getStateAtPosition(length-1);
						tuple[0] = counter; //Location of the OUT BRANCH in the counterexample.
						//// Computing the location of the IN-BRANCH					
						for(int j = 0; j<counterexample.getLength();j++)
						{
							IPredicate counter_example_state = counterexample.getStateAtPosition(j);
							if(last_state_of_the_path.equals(counter_example_state))
							{
								tuple[1] = j; // Location of the state in the counter example where the branch ends
								//m_Logger.warn(" LAST STATE OF THE PATH -->> " + j);
							}
						}
						//// In-Branch Location computed.
						result.add(tuple);
						m_Logger.warn(" ");
					}
				}
			}
		}
		m_Logger.warn(" ");
		return result;
	}

	private ArrayList<CodeBlock> RelevantStatementInBranch(int branch_start, int branch_end, NestedWord<CodeBlock> counterexampleWord, ArrayList<int[]> informationFromCFG, IPredicate weakest_precondition_1, SmtManager smtManager, ModifiableGlobalVariableManager modGlobVarManager)
	{
		m_Logger.warn("Entered RelevantStatementInBranch ");
		ArrayList<CodeBlock> result = new ArrayList<>();
		PredicateTransformer pt = new PredicateTransformer(smtManager.getPredicateFactory(), smtManager.getVariableManager(), smtManager.getScript(), modGlobVarManager, m_Services);
		FaultLocalizationRelevanceChecker rc = new FaultLocalizationRelevanceChecker(smtManager.getManagedScript(), modGlobVarManager, smtManager.getBoogie2Smt());
		
		//int[] tuple = new int[2];
		//tuple[0]=4;
		//tuple[1]=6;
		//informationFromCFG.add(tuple);

		IPredicate weakest_precondition_2 = null;
		IPredicate pre_precondition_1 = null;
		CodeBlock statement_1 = null;
		ERelevanceStatus relevance = null;
		
		for(int backward_counter = branch_end; backward_counter>=branch_start; backward_counter--) // Move Backward in the branch.
		{
			int flag = 0;
			int use_markhor =0;
			int a = 0; // branch out
			int b = 0; // branch in
			for(int j = 0; j<informationFromCFG.size();j++)
			{
				if (backward_counter == informationFromCFG.get(j)[1]-1)
				{
					flag = 1; // Current Statement is a branch in statement.
					a = informationFromCFG.get(j)[0];
					b = informationFromCFG.get(j)[1]-1;
				}
			}
			
			if(flag==1) // Current Statement is a branch in statement.
			{
				m_Logger.warn("branch in statement");				
				// Check if the branch is relevant.
				IPredicate weakest_precondition_1_temp = weakest_precondition_1;
				// Computing the markhor formula of the branch.
				TransFormula combined_transition_formula = counterexampleWord.getSymbolAt(a).getTransitionFormula();
				for(int i = a+1 ; i <= b;i++)
				{
					CodeBlock statement = counterexampleWord.getSymbolAt(i);
					TransFormula transition_formula = statement.getTransitionFormula();
					combined_transition_formula = TransFormula.sequentialComposition(m_Logger, m_Services, smtManager.getBoogie2Smt(),
							false, false, false, combined_transition_formula, transition_formula);
				}
				TransFormula markhor = TransFormula.computeMarkhorTransFormula(combined_transition_formula, smtManager.getBoogie2Smt(), 
						m_Services, m_Logger);
				
				
				// Check the relevance of the branch by the new method.
				weakest_precondition_2 = weakest_precondition_1;
				weakest_precondition_1 = pt.weakestPrecondition(weakest_precondition_1, markhor);
				pre_precondition_1 = smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(weakest_precondition_1));
				statement_1 = counterexampleWord.getSymbol(backward_counter+1);
				String preceeding = statement_1.getPreceedingProcedure(); // ????
				String succeding = statement_1.getSucceedingProcedure(); // ????
				BasicInternalAction basic = new BasicInternalAction(preceeding,succeding, markhor);
	
				relevance = rc.relevanceInternal(pre_precondition_1, basic, smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(weakest_precondition_2)));
				if(relevance == ERelevanceStatus.InUnsatCore) //Branch is RELEVANT
				{
					use_markhor=1;
					m_Logger.warn("THE BRANCH IS RELEVANT");
					// Check which statements in the branch are relevant.
					ArrayList<CodeBlock> relevant_statements =  RelevantStatementInBranch(a, b, counterexampleWord ,informationFromCFG, weakest_precondition_1, smtManager, modGlobVarManager);
					result.addAll(relevant_statements);
					
					weakest_precondition_1 = pt.weakestPrecondition(weakest_precondition_1, markhor);
				}
				else
				{
					weakest_precondition_1 = weakest_precondition_1_temp;
				}
							
				
				
				backward_counter = a ; //Just before the branch.
			}
			else  // The statement under consideration is not a branch-in statement.
			{
				weakest_precondition_2 = weakest_precondition_1;
				weakest_precondition_1 = pt.weakestPrecondition(weakest_precondition_1, counterexampleWord.getSymbolAt(backward_counter).getTransitionFormula());
				pre_precondition_1 = smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(weakest_precondition_1));
				statement_1 = counterexampleWord.getSymbolAt(backward_counter);
				BasicInternalAction basic = new BasicInternalAction(statement_1.getPreceedingProcedure(),statement_1.getSucceedingProcedure(), statement_1.getTransitionFormula());
				
				relevance = rc.relevanceInternal(pre_precondition_1, basic, smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(weakest_precondition_2)));
				if(relevance  == ERelevanceStatus.InUnsatCore)
				{
					m_Logger.warn("RELEVANT");
					m_Logger.warn(statement_1);
					result.add(statement_1);
					
				}
			}
			
			

		}
		
		
		
		return result;
		
	}
	
	
	private boolean BranchRelevanceChecker(int a, int b, IPredicate weakestPreconditionOld, NestedWord<CodeBlock> counterexampleWord, SmtManager smtManager, ModifiableGlobalVariableManager modGlobVarManager)
	{
		PredicateTransformer pt = new PredicateTransformer(smtManager.getPredicateFactory(), smtManager.getVariableManager(), smtManager.getScript(), modGlobVarManager, m_Services);
		TransFormula combinedTransitionFormula = counterexampleWord.getSymbolAt(b).getTransitionFormula();
		FaultLocalizationRelevanceChecker rc = new FaultLocalizationRelevanceChecker(smtManager.getManagedScript(), modGlobVarManager, smtManager.getBoogie2Smt());
		for(int i = a+1; i<=b; i++)
		{
			CodeBlock Statement = counterexampleWord.getSymbol(i);
			TransFormula TransitionFormula = Statement.getTransitionFormula();
			combinedTransitionFormula = TransFormula.sequentialComposition(m_Logger, m_Services, smtManager.getBoogie2Smt(), false, false, false, combinedTransitionFormula,TransitionFormula);
		}
		TransFormula markhor = TransFormula.computeMarkhorTransFormula(combinedTransitionFormula, smtManager.getBoogie2Smt(), m_Services, m_Logger);
		IPredicate weakestPreconditionNew = pt.weakestPrecondition(weakestPreconditionOld, markhor);
		IPredicate pre = smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(weakestPreconditionNew));
		String preceeding = counterexampleWord.getSymbolAt(a-1).getPreceedingProcedure();
		String succeeding = counterexampleWord.getSymbolAt(b+1).getSucceedingProcedure();
		BasicInternalAction basic = new BasicInternalAction(preceeding, succeeding, markhor);
		
		ERelevanceStatus relevance = rc.relevanceInternal(pre, basic, weakestPreconditionOld);
		if(relevance == ERelevanceStatus.InUnsatCore || relevance == ERelevanceStatus.Sat) // Branch is RELEVANT
		{
			return true;
		}
		else // BRANCH IS NOT RELEVANT
		{
			return false;
		}
	}
	private void computeFlowSensitiveTraceFormula(IRun<CodeBlock, IPredicate> counterexampleRun,
		IPredicate falsePredicate, ModifiableGlobalVariableManager modGlobVarManager, SmtManager smtManager, ArrayList<int[]> informationFromCFG) 
	
	{
		NestedWord<CodeBlock> counterexampleWord = (NestedWord<CodeBlock>) counterexampleRun.getWord();
		PredicateTransformer pt = new PredicateTransformer(smtManager.getPredicateFactory(), smtManager.getVariableManager(), smtManager.getScript(), modGlobVarManager, m_Services);
		FaultLocalizationRelevanceChecker rc = new FaultLocalizationRelevanceChecker(smtManager.getManagedScript(), modGlobVarManager, smtManager.getBoogie2Smt());
		
		if (false) {
			// 2016-04-01 Matthias: Code for computing sequence of weakest precondition
			// that is also correct for traces with calls and returns.
			final IterativePredicateTransformer ipt = new IterativePredicateTransformer(
					smtManager.getPredicateFactory(), smtManager.getVariableManager(), 
					smtManager.getScript(), smtManager.getBoogie2Smt(), modGlobVarManager, 
					m_Services, counterexampleWord, null, falsePredicate, null);
			final DefaultTransFormulas dtf = new DefaultTransFormulas(counterexampleWord, 
					null, falsePredicate, Collections.emptySortedMap(), modGlobVarManager, false);
			final InterpolantsPreconditionPostcondition weakestPreconditionSequence = 
					ipt.computeWeakestPreconditionSequence(dtf, Collections.emptyList());
			// construction of this list might be superfluous because we can also
			// iterate over the InterpolantsPreconditionPostcondition object
			final List<IPredicate> weakestPreconditionList = new ArrayList<>();
			for (int i=0; i < counterexampleWord.length()+1; i++) {
				weakestPreconditionList.add(weakestPreconditionSequence.getInterpolant(i));
			}
		}
		
		// Non-Flow Sensitive INCREMENTAL ANALYSIS
		m_Logger.warn("Initializing Non-Flow Sensitive INCREMENTAL ANALYSIS . . .");

		ArrayList<CodeBlock> relevant = new ArrayList<>(); //Will store the terms relevant for the error.
		ArrayList<IPredicate> weakest_precondition_list = new ArrayList<>();
		ArrayList<IPredicate> pre_precondition_list = new ArrayList<>();
		
		int backward_counter = counterexampleWord.length();
		
		//Relevency Information of the last statement
		IRelevanceInformation relevancy_of_statement = new RelevanceInformation();
		((RelevanceInformation) relevancy_of_statement).setStatement(counterexampleWord.getSymbolAt(backward_counter-1));
		Relevance_of_statements.add(relevancy_of_statement);
		
		IPredicate weakest_precondition = smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().constructFalse()); // FALSE for WP(False, error_trace)

		for(int j = counterexampleWord.length() - 1; j>=0; j--)
		{
			CodeBlock statement = counterexampleWord.getSymbolAt(j);
			TransFormula transition_formula = statement.getTransitionFormula();
			weakest_precondition = pt.weakestPrecondition(weakest_precondition, transition_formula);
			weakest_precondition_list.add(weakest_precondition);
			pre_precondition_list.add(smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(weakest_precondition)));
			

				
		}
		int wp_counter = 0;
		int pre_counter = wp_counter + 1;
		for(int i = backward_counter-2 ; i >= 0; i--)
		{

			
				
				CodeBlock statement = counterexampleWord.getSymbolAt(i);
				TransFormula a = statement.getTransitionFormula();
				// Relevancy Information.
				relevancy_of_statement = new RelevanceInformation();
				((RelevanceInformation) relevancy_of_statement).setStatement(statement);
				
				BasicInternalAction basic = new BasicInternalAction(statement.getPreceedingProcedure(),statement.getSucceedingProcedure(), statement.getTransitionFormula());
				
				
				
				IPredicate wp = weakest_precondition_list.get(wp_counter);
				IPredicate pre = pre_precondition_list.get(pre_counter);
				
				ERelevanceStatus relevance = rc.relevanceInternal(pre, basic, smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(wp)));
				if(relevance  == ERelevanceStatus.InUnsatCore) // This is the case when the the triple is unsatisfiable and the statment is in the Unsatisfiable core.
				{
					//m_Logger.warn("RELEVANT");
					//m_Logger.warn(statement);
					relevant.add(statement);
					// SET CRITERIA 1 TO TRUE
					((RelevanceInformation) relevancy_of_statement).setCriteria1(true);
					
				}
				else if(relevance == ERelevanceStatus.Sat) // The case when we have HAVOC statements. In this case the statement is relevant if the triple is satisfiable.
				{
					relevant.add(statement);
					((RelevanceInformation) relevancy_of_statement).setCriteria1(true);
				}
				else
				{
					// ToDo ! 
					// ADD here UNKNOWN ! after changing the criteria data type to ENUM.
				}
				wp_counter = wp_counter + 1;
				pre_counter = pre_counter + 1;
				// Adding relevancy information in the array list Relevance_of_statements.
				Relevance_of_statements.add(relevancy_of_statement);
			
			
		}
		
		// INITIALIZING FLOW SENSITIVE ANALYSIS.
		m_Logger.warn("Initializing FLOW SENSITIVE analysis");
		// Main trace
		IPredicate weakestPreconditionOld = smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().constructFalse());
		IPredicate weakestPreconditionNew = smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().constructFalse());
		IPredicate weakestPreconditionTemp = null;
		IPredicate pre = null;
		for ( int backwardcounter = counterexampleWord.length() - 1; backwardcounter >= 0 ; backwardcounter -- )
		{
			CodeBlock Statement = counterexampleWord.getSymbol(backwardcounter);
			int flag = 0;
			int a =0;
			int b = 0;
			// Find out if the current Statement is a BRANCH-IN statement.
			for(int j =0; j<informationFromCFG.size(); j++)
			{
				if(backwardcounter == informationFromCFG.get(j)[1]-1)
				{
					flag = 1; // Yes it is a Branch-IN statement.
					a = informationFromCFG.get(j)[0];
					b = informationFromCFG.get(j)[1]-1;
				}
			}
			if(flag == 1) // The current statement is a BRANCH-IN Statement.
			{
				// Check the relevancy of the branch ?
				boolean c =  BranchRelevanceChecker(a,b,weakestPreconditionOld,counterexampleWord,smtManager,modGlobVarManager);
				
					
			}
			else // The statement under consideration is NOT a BRANCH-IN Statement.
			{
				weakestPreconditionOld = weakestPreconditionNew;
				weakestPreconditionNew = pt.weakestPrecondition(weakestPreconditionOld, counterexampleWord.getSymbolAt(backwardcounter).getTransitionFormula());
				pre = smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(weakestPreconditionNew));
				Statement = counterexampleWord.getSymbolAt(backwardcounter);
				BasicInternalAction basic = new BasicInternalAction(Statement.getPreceedingProcedure(), Statement.getPreceedingProcedure(), Statement.getTransitionFormula());
				ERelevanceStatus relevence = rc.relevanceInternal(pre, basic, smtManager.getPredicateFactory().newPredicate(smtManager.getPredicateFactory().not(weakestPreconditionOld)));
				if(relevence == ERelevanceStatus.InUnsatCore || relevence == ERelevanceStatus.Sat)
				{
					int q = 0;
					// RELEVANT With respect to the flow sensitive analysis !
				}
			}
			
			
		}
		// Start to analyse from backwards
		// If you encounter a branch then check if the branch is relevant?  Make a Function:  Bool BranchRelevanceChecker();
		// If it is relevant Then go inside the branch and do the analysis from behind
		// Recursion
		// Come out of the branch and give the full results.
		
	}

	/**
	 * Check if there is a path from startPoint so some element of the 
	 * possibleEndPoints set.
	 * If yes, a NestedRun is returned, otherwise null is returned.
	 * 
	 * @throws ToolchainCanceledException if toolchain was cancelled (e.g., 
	 * because of a timeout)
	 */
	private NestedRun<CodeBlock, IPredicate> findPathInCFG(IPredicate startPoint, 
			Set<IPredicate> possibleEndPoints, INestedWordAutomaton<CodeBlock, 
			IPredicate> cfg) 
	{

		
		try 
		{
			return (new IsEmpty<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services), cfg, 
					Collections.singleton(startPoint), possibleEndPoints)).getNestedRun();
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
	public ArrayList<IRelevanceInformation> getRelevanceInformation() 
	{
		for(int i= 0;i <Relevance_of_statements.size()/2;i++)
		{
			IRelevanceInformation temp = Relevance_of_statements.get(i);
			Relevance_of_statements.set(i, Relevance_of_statements.get(Relevance_of_statements.size()-i-1));
			Relevance_of_statements.set(Relevance_of_statements.size()-i-1, temp);
		}
		m_Logger.warn("- - - - - - - -");
		for(int i= 0;i <Relevance_of_statements.size();i++)
		{
			m_Logger.warn(((RelevanceInformation) Relevance_of_statements.get(i)).getStatement() +" | " +Relevance_of_statements.get(i).getShortString());
		}
		return Relevance_of_statements;
	}
	
}
