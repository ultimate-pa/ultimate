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
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.DefaultTransFormulas;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.NestedFormulas;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.NestedSsaBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.result.IRelevanceInformation;
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

	public FlowSensitiveFaultLocalizer(IRun<CodeBlock, IPredicate> counterexample,
			INestedWordAutomaton<CodeBlock, IPredicate> cfg, IUltimateServiceProvider services, SmtManager smtManager,
			ModifiableGlobalVariableManager modGlobVarManager, PredicateUnifier predicateUnifier) {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		m_Logger.warn("* * * ENTERED FLOW SENSITIVE FAULT LOCALIZER * * * *");
		ArrayList<int[]> informationFromCFG = computeInformationFromCFG( (NestedRun<CodeBlock, IPredicate>) counterexample, cfg); //Get branch information. in the form of an array list
		IPredicate errorPrecondition = computeErrorPrecondition((NestedWord<CodeBlock>) counterexample.getWord(), smtManager, predicateUnifier, modGlobVarManager, informationFromCFG);
		computeFlowSensitiveTraceFormula(errorPrecondition, counterexample, predicateUnifier.getFalsePredicate(), modGlobVarManager, smtManager,informationFromCFG);
	}

	@SuppressWarnings("null")
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
		PredicateTransformer pt = new PredicateTransformer(smtManager, modGlobVarManager, m_Services);
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
				pre_precondition_1 = smtManager.newPredicate(smtManager.not(weakest_precondition_1));
				statement_1 = counterexampleWord.getSymbol(backward_counter+1);
				String preceeding = statement_1.getPreceedingProcedure(); // ????
				String succeding = statement_1.getSucceedingProcedure(); // ????
				BasicInternalAction basic = new BasicInternalAction(preceeding,succeding, markhor);
	
				relevance = rc.relevanceInternal(pre_precondition_1, basic, smtManager.newPredicate(smtManager.not(weakest_precondition_2)));
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
				pre_precondition_1 = smtManager.newPredicate(smtManager.not(weakest_precondition_1));
				statement_1 = counterexampleWord.getSymbolAt(backward_counter);
				BasicInternalAction basic = new BasicInternalAction(statement_1.getPreceedingProcedure(),statement_1.getSucceedingProcedure(), statement_1.getTransitionFormula());
				
				relevance = rc.relevanceInternal(pre_precondition_1, basic, smtManager.newPredicate(smtManager.not(weakest_precondition_2)));
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
	
	
	private void computeFlowSensitiveTraceFormula(IPredicate errorPrecondition, IRun<CodeBlock, IPredicate> counterexampleRun,
		IPredicate falsePredicate, ModifiableGlobalVariableManager modGlobVarManager, SmtManager smtManager, ArrayList<int[]> informationFromCFG) 
	
	{
		NestedWord<CodeBlock> counterexampleWord = (NestedWord<CodeBlock>) counterexampleRun.getWord();
		DefaultTransFormulas nestedTransFormulas = new DefaultTransFormulas(counterexampleWord, errorPrecondition, falsePredicate, new TreeMap<>(), modGlobVarManager, false);
		NestedSsaBuilder ssaBuilder = new NestedSsaBuilder(counterexampleWord, smtManager, nestedTransFormulas, modGlobVarManager, m_Logger, false);
		NestedFormulas<Term, Term> ssa = ssaBuilder.getSsa();
		PredicateTransformer pt = new PredicateTransformer(smtManager, modGlobVarManager, m_Services);
		FaultLocalizationRelevanceChecker rc = new FaultLocalizationRelevanceChecker(smtManager.getManagedScript(), modGlobVarManager, smtManager.getBoogie2Smt());
		
		
		
		// Non-Flow Sensitive INCREMENTAL ANALYSIS
		m_Logger.warn("Doing Incremental Analysis . . .");

		ArrayList<CodeBlock> relevant = new ArrayList<>(); //Will store the terms relevant for the error.
		ArrayList<IPredicate> weakest_precondition_list = new ArrayList<>();
		ArrayList<IPredicate> pre_precondition_list = new ArrayList<>();
		
		int backward_counter = counterexampleWord.length();

		IPredicate weakest_precondition = smtManager.newFalsePredicate(); // FALSE for WP(False, error_trace)
		for(int j = counterexampleWord.length() - 1; j>=0; j--)
		{
			CodeBlock statement = counterexampleWord.getSymbolAt(j);
			TransFormula transition_formula = statement.getTransitionFormula();
			weakest_precondition = pt.weakestPrecondition(weakest_precondition, transition_formula);
			weakest_precondition_list.add(weakest_precondition);
			pre_precondition_list.add(smtManager.newPredicate(smtManager.not(weakest_precondition)));
				
		}
		int wp_counter = 0;
		int pre_counter = wp_counter + 1;
		for(int i = backward_counter-2 ; i >= 0; i--)
		{

			

				CodeBlock statement = counterexampleWord.getSymbolAt(i);
				TransFormula a = statement.getTransitionFormula();
				

				BasicInternalAction basic = new BasicInternalAction(statement.getPreceedingProcedure(),statement.getSucceedingProcedure(), statement.getTransitionFormula());
				
				
				
				IPredicate wp = weakest_precondition_list.get(wp_counter);
				IPredicate pre = pre_precondition_list.get(pre_counter);
				
				ERelevanceStatus relevance = rc.relevanceInternal(pre, basic, smtManager.newPredicate(smtManager.not(wp)));
				if(relevance.toString() == "InUnsatCore")
				{
					m_Logger.warn("RELEVANT");
					m_Logger.warn(statement);
					relevant.add(statement);
					
				}
				wp_counter = wp_counter + 1;
				pre_counter = pre_counter + 1;

			
			
		}
		///////////////////////////////////////////////////////////////////////- - - - DONE WITH NON-FLOW SENSITIVE INCREMENTAL ANALYSIS --- //////////////////////////////// 
		
		///////////////////////////////                          STARTING INCREMENTAL flow sensitive FAULT LOCALIZATION //////////////////
		m_Logger.warn("Starting incremental flow sensitive fault localization. . . . ");
		
		ArrayList<CodeBlock> relevant_statements = new ArrayList<>();
		IPredicate weakest_precondition_1 = smtManager.newFalsePredicate();
		IPredicate weakest_precondition_2 = null;
		IPredicate pre_precondition_1 = null;
		CodeBlock statement_1 = null;
		ERelevanceStatus relevance = null;
		
		ArrayList<TransFormula> trans_formula_arraylist = new ArrayList<>();
		backward_counter = counterexampleWord.length()-1;
		int flag = 0;
		int use_markhor =0;
		while(backward_counter != -1)
		{
			flag = 0;
			use_markhor =0;
			int a = 0; // branch out
			int b = 0; // branch in
			for(int i = 0; i<informationFromCFG.size();i++)
			{
				if (backward_counter == informationFromCFG.get(i)[1]-1)
				{
					flag = 1;
					a = informationFromCFG.get(i)[0];
					b = informationFromCFG.get(i)[1]-1;
				}
			}

			if(flag == 1) // Compute the markhor formula of the branch and check the relevance of the branch.
			{			
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
				pre_precondition_1 = smtManager.newPredicate(smtManager.not(weakest_precondition_1));
				statement_1 = counterexampleWord.getSymbol(backward_counter+1);
				String preceeding = statement_1.getPreceedingProcedure(); // ????
				String succeding = statement_1.getSucceedingProcedure(); // ????
				BasicInternalAction basic = new BasicInternalAction(preceeding,succeding, markhor);
				relevance = rc.relevanceInternal(pre_precondition_1, basic, smtManager.newPredicate(smtManager.not(weakest_precondition_2)));
				if(relevance == ERelevanceStatus.InUnsatCore)
				{
					use_markhor=1;
					m_Logger.warn("THE BRANCH IS RELEVANT");
					// Check which statements in the branch are relevant.
					relevant_statements.addAll(RelevantStatementInBranch(a, b, counterexampleWord ,informationFromCFG, weakest_precondition_1, smtManager, modGlobVarManager));
					
					
					
				}
				else // If the branch is not relevant, use the previous weakest pre-condition.
				{
					weakest_precondition_1 = weakest_precondition_1_temp;
				}
							
				
				
				backward_counter = a - 1 ; //Just before the branch.
			}
			else // The statement under consideration is not a branch-in statement.
			{ 	
				weakest_precondition_2 = weakest_precondition_1;
				weakest_precondition_1 = pt.weakestPrecondition(weakest_precondition_1, counterexampleWord.getSymbolAt(backward_counter).getTransitionFormula());
				pre_precondition_1 = smtManager.newPredicate(smtManager.not(weakest_precondition_1));
				statement_1 = counterexampleWord.getSymbolAt(backward_counter);
				BasicInternalAction basic = new BasicInternalAction(statement_1.getPreceedingProcedure(),statement_1.getSucceedingProcedure(), statement_1.getTransitionFormula());
				
				relevance = rc.relevanceInternal(pre_precondition_1, basic, smtManager.newPredicate(smtManager.not(weakest_precondition_2)));
				if(relevance  == ERelevanceStatus.InUnsatCore)
				{
					m_Logger.warn("RELEVANT");
					m_Logger.warn(statement_1);
					relevant_statements.add(statement_1);
					
				}
				
				
				backward_counter -= 1;
			}
		}
		
		// COMPUTE THE ERROR PRE-CONDITION FROM THE TRANSFORMULAS IN  "trans_formula_arraylist" on forward order.
		
		
		// Step 2.5:
		// see if it is relevant or not ??
		
		// step 3:
		// if it is not relevant, just ignore the branch.
		
		// IF IT IS RELEVANT. 
		// Go further into the branch.
		
		///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
		m_Logger.warn("Computing Flow Sensitive Formula . . . .");

		m_Logger.warn(" ");
		m_Logger.warn("Precondition : " + ssa.getPrecondition());
		m_Logger.warn("Precondition : " + errorPrecondition);
		m_Logger.warn("Branching Information");
		for(int i = 0; i<informationFromCFG.size();i++)
		{
				m_Logger.warn("Branch out " + informationFromCFG.get(i)[0]);
				m_Logger.warn("Branch in " + informationFromCFG.get(i)[1]);
		}
		
		m_Logger.warn(" ");
		//////////////////////////////////////////// - - FORMULA WITH CONJUNCTS - - ////////////////////////////////////////
		ArrayList<Term> formulas_list = new ArrayList<Term>(); // initializing a new array list that will be later turned to conjuncts
		//formulas_list.add(Util.not(smtManager.getScript(), ssa.getPrecondition())); // adding the precondition in the array
		for(int k = 0; k < counterexampleWord.length(); k++)
		{
			formulas_list.add(ssa.getFormulaFromNonCallPos(k));
		}
		Term conjunct_formula = SmtUtils.and(smtManager.getScript(), formulas_list); //make conjuncts from a list of formulas.
		//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
		m_Logger.warn(" ");
		//////////////////////////////////////////- - FORMULA WITH only IMPLICATIONS - - ////////////////////////////
		Term right_side;
		Term implication_formula = Util.implies(smtManager.getScript(), ssa.getFormulaFromNonCallPos(0)); //First line in the program
		//Term implication_formula = Util.implies(smtManager.getScript(), Util.not(smtManager.getScript(), ssa.getPrecondition())); // adding precondition as the first formula
		for(int k = 1; k < counterexampleWord.length()-1; k++)
		{
			right_side = ssa.getFormulaFromNonCallPos(k); // Formula that will be put on the right side of the implication
			implication_formula = Util.implies(smtManager.getScript(), implication_formula, right_side); 
		}
		//////////////////////////////////////////////////////////////////////////////////////////////////////////	
		m_Logger.warn(" ");
		//////////////////////////////////////// - - - PRO SENSITIVE FORMULA //////////////////////////////////
		ArrayList<Term> prosensitive_formula_list = new ArrayList<Term>(); // A main list of the forumlas that will be put into conjunctions.
		ArrayList<Term> implication_formula_list = new ArrayList<Term>(); // Main list of all the formulas which contain formulas of the form
																		  // guard(body) ==> body.
		// Computation of the implication_formula_list.
		for(int i =0; i < informationFromCFG.size();i++)
		{
			int[] Branch = informationFromCFG.get(i);
			int branch_out_formula = Branch[0];
			int branch_in_formula = Branch[1];
			ArrayList<Term> right_conjunct_formulas_list = new ArrayList<Term>();
			for(int j = branch_out_formula+1; j < branch_in_formula; j++)
			{
				right_conjunct_formulas_list.add(ssa.getFormulaFromNonCallPos(j));
			}
			Term right_conjunct_formula = SmtUtils.and(smtManager.getScript(), right_conjunct_formulas_list);
			Term left_side_of_implication = ssa.getFormulaFromNonCallPos(branch_out_formula);
			Term pro_sensitive_implication = Util.implies(smtManager.getScript(), left_side_of_implication, right_conjunct_formula);
			implication_formula_list.add(pro_sensitive_implication);
		}
		for(int k = 0; k <counterexampleWord.length()-1; k++)
		{
			boolean flag1 = false;
			for(int l=0;l<informationFromCFG.size();l++) // Check if the current formula is at a branch out position.
			{
				if(k == informationFromCFG.get(l)[0])
				{
					flag1 = true; //current formula is at a branch out position
					k = informationFromCFG.get(l)[1] - 1;
				}
			}
			if(!flag1)
			{
				prosensitive_formula_list.add(ssa.getFormulaFromNonCallPos(k));
			}
		}
		// Now add the implications in the pro sensitive formula list
		for(int k = 0; k < implication_formula_list.size(); k++ )
		{
			prosensitive_formula_list.add(implication_formula_list.get(k)); // FINAL CONJUNTS OF THE PRO-SENSITIVE FORMULA
		}
		// Make conjuncts
		Term pro_flow_sensitive_formula = SmtUtils.and(smtManager.getScript(), prosensitive_formula_list);	
		m_Logger.warn(" ");
		/////////////////////////////////////////////////// END OF PRO-FLOW SENSITIVE COMPUTATION /////////////////////////////////////////////////
		
		/////////////////////////////////////// - - TRANSFORM INTO CONJUNCTIVE NORMAL FORM - - ////////
		Cnf cnf = new Cnf(smtManager.getScript(), m_Services , smtManager.getVariableManager());
		Term conjunctive_normal_form = cnf.transform(pro_flow_sensitive_formula); //Term is a formula 
		Term[] conjunt_array = SmtUtils.getConjuncts(conjunctive_normal_form);
		//m_Logger.warn("CONJUNCTS IN CNF = " + conjunt_array);
		//////////////////////////////////////////////////////////////////////////////////////////////
		m_Logger.warn(" ");

		smtManager.getScript().push(1);
		//Term precondition = Util.not(smtManager.getScript(), ssa.getPrecondition()); // FEEDING THE COMPLIMENT OF THE PRECONDITION
		Term precondition =  ssa.getPrecondition(); // Feeding the normal precondition
		String name = "Pre-condition";
		Annotation annot = new Annotation(":named", name);
		Term annotTerm = smtManager.getScript().annotate(precondition, annot);
		smtManager.assertTerm(annotTerm);
		
		Term term;
		for(int i=0; i< conjunt_array.length; i++)
		{
			term = conjunt_array[i] ; 
			name = "Formula" + i;
			annot = new Annotation(":named", name);
			annotTerm = smtManager.getScript().annotate(term, annot);
			smtManager.assertTerm(annotTerm);
		}
		
		Term neg_post_cond = ssa.getFormulaFromNonCallPos(counterexampleWord.length()-1);
		name = "post-condition";
		annot = new Annotation(":named", name);
		annotTerm = smtManager.getScript().annotate(Util.not(smtManager.getScript(),neg_post_cond ), annot);
		smtManager.assertTerm(annotTerm);
		
		
		LBool sat = smtManager.getScript().checkSat();
		
		
		
		m_Logger.warn(sat);
		m_Logger.warn(" "); 
		 
		
		Term[] unsat_core = smtManager.getScript().getUnsatCore();
		m_Logger.warn(" ");
		
		
		m_Logger.warn(ssaBuilder.toString());
		
	}

	private IPredicate computeErrorPrecondition(NestedWord<CodeBlock> counterexample, SmtManager smtManager,
			PredicateUnifier predicateUnifier, ModifiableGlobalVariableManager modGlobVarManager,ArrayList<int[]> informationFromCFG)
	{
		m_Logger.warn("COMPUTING ERROR PRECONDITION . . . . . ");
		PredicateTransformer pt = new PredicateTransformer(smtManager, modGlobVarManager, m_Services);
		// iterate over the counterexample and compute the error precondition		
		// Make an ArrayList of Transition formulas in a backward fashion. 
		ArrayList<TransFormula> trans_formula_arraylist = new ArrayList<>();
		int backward_counter = counterexample.length()-1;
		int flag = 0;
		while(backward_counter != -1)
		{
			flag = 0;
			int a = 0; // branch out
			int b = 0; // branch in
			for(int i = 0; i<informationFromCFG.size();i++)
			{
				if (backward_counter == informationFromCFG.get(i)[1]-1)
				{
					flag = 1;
					a = informationFromCFG.get(i)[0];
					b = informationFromCFG.get(i)[1]-1;
				}
			}
			if(flag == 1) // compute the markhor Transformula and push it into the transformula array list here .
			{			// also update backward counter ! 
				TransFormula combined_transition_formula = counterexample.getSymbolAt(a).getTransitionFormula();
				for(int i = a+1 ; i <= b;i++)
				{
					CodeBlock statement = counterexample.getSymbolAt(i);
					TransFormula transition_formula = statement.getTransitionFormula();
					combined_transition_formula = TransFormula.sequentialComposition(m_Logger, m_Services, smtManager.getBoogie2Smt(),
							false, false, false, combined_transition_formula, transition_formula);
				}
				TransFormula markhor = TransFormula.computeMarkhorTransFormula(combined_transition_formula, smtManager.getBoogie2Smt(), 
						m_Services, m_Logger);
				trans_formula_arraylist.add(markhor);
				backward_counter = a - 1 ;
			}
			else // push the transformula at this position to the trans_formula_arraylist.
			{ 	// also update the backward counter !
				trans_formula_arraylist.add(counterexample.getSymbolAt(backward_counter).getTransitionFormula());
				backward_counter -= 1;
			}
		}
		// COMPUTE THE ERROR PRE-CONDITION FROM TTHE TRANSFORMULAS IN  "trans_formula_arraylist" on forward order.
		IPredicate weakest_precondition = smtManager.newFalsePredicate(); // initialization to false
		for(int i=0; i< trans_formula_arraylist.size(); i++)
		{
			weakest_precondition = pt.weakestPrecondition(weakest_precondition, trans_formula_arraylist.get(i));
		}
		return weakest_precondition;
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
	public List<IRelevanceInformation> getRelevanceInformation() {
		//TODO implement this
		
		throw new AssertionError("not yet implemented");
	}
	
}