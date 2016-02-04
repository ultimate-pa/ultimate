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

import java.awt.List;
import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.TreeMap;
import org.apache.log4j.Logger;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.Tuple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Cnf;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.DefaultTransFormulas;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.NestedFormulas;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.NestedSsaBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.AnnotateAndAssertCodeBlocks;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
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
		//ArrayList<int[]> informationFromCFG = computeInformationFromCFG( (NestedRun<CodeBlock, IPredicate>) counterexample, cfg); //Get branch information. in the form of an array list
		computeFlowSensitiveTraceFormula(errorPrecondition, counterexample, predicateUnifier.getFalsePredicate(), modGlobVarManager, smtManager,informationFromCFG);
	}

	@SuppressWarnings("null")
	private ArrayList<int[]> computeInformationFromCFG(NestedRun<CodeBlock, IPredicate> counterexample,
			INestedWordAutomaton<CodeBlock, IPredicate> cfg) 
	{
		m_Logger.warn("* * * ENTERED COMPUTE INFORMATION FROM CFG * * * ");
		ArrayList<IPredicate> out_branches = new ArrayList<>();
		ArrayList<IPredicate> in_branches = new ArrayList<>();
		int[] tuple = new int[2];
		ArrayList<int[]> result = new ArrayList<>();
		int size = counterexample.getStateSequence().size();
		m_Logger.warn(counterexample);
		m_Logger.warn(" ");
		IPredicate start_state = null;
		// For each state find out if it's a branch or not.
		// For each state, find out if there is an outgoing branch from that state
		// that transitions to a state which is not in the counter example.
		// if you find such a state, then from that state. run the FINDPATHINCFG() method
		// and find out if that path returns to a state which IS in the counterexample.
		// If you find such a path, then that state is a branching state then you save this information for future use.
		
		// REMEMBER THE CASE WHEN THERE ARE TWO OUTGOING BRANCHES FROM A STATE GOING IN THE SAME BRANCH.
		start_state = counterexample.getStateAtPosition(1);
		Iterable<OutgoingInternalTransition<CodeBlock, IPredicate>> succesors = cfg.internalSuccessors(start_state);
		Set<IPredicate> possibleEndPoints =  new HashSet<IPredicate>();  // all the successive paths.
		for(int j=2; j< size; j++)
		{
			possibleEndPoints.add((IPredicate) counterexample.getStateAtPosition(j));
		}
		for( OutgoingInternalTransition<CodeBlock, IPredicate> test:succesors)
		{
			IPredicate succesor2 = test.getSucc();
			if(succesor2 != counterexample.getStateAtPosition(2))
			{
				m_Logger.warn("Found a state not in the counter example -->>" + succesor2);
				 NestedRun<CodeBlock, IPredicate> path = findPathInCFG(succesor2, possibleEndPoints, cfg);
				m_Logger.warn("Path -->  "+ path);
				if(path != null)
				{
					// Found an IF branch at position 1 of the counter example.
					int length = path.getLength();
					IPredicate last_state_of_the_path = path.getStateAtPosition(length-1);
					out_branches.add(start_state);
					in_branches.add(last_state_of_the_path);
					tuple[0] = 1; //Location of the OUT BRANCH in the counterexample.
					
					//// Computing the location of the IN-BRANCH					
					for(int j = 0; j<counterexample.getLength();j++)
					{
						IPredicate counter_example_state = counterexample.getStateAtPosition(j);
						if(last_state_of_the_path.equals(counter_example_state))
						{
							tuple[1] = j;
							m_Logger.warn(" LAST STATE OF THE PATH -->> " + j);
						}
					}
					
					
					//// In-Branch Location computed.
					result.add(tuple);
					m_Logger.warn(" ");
				}
			}
		}
		m_Logger.warn(" ");
		/*for(int i=0; i < size; i ++)
		{
			start_state = counterexample.getStateAtPosition(i);
			m_Logger.warn("START STATE ->> " + start_state);
			Set<IPredicate> possibleEndPoints =  new HashSet<IPredicate>();  // all the successive paths.
			for(int j=i+1; j< size; j++)
			{
				possibleEndPoints.add((IPredicate) counterexample.getStateAtPosition(j));
			}
			
			m_Logger.warn("POSSIBLE END POINTS SET ->>" + possibleEndPoints);
			Object path = findPathInCFG(start_state, possibleEndPoints, cfg);
			m_Logger.warn("Branching Inormation ->> " + path);
			m_Logger.warn(" ");
		}*/

		int[] tuplezz = result.get(0);
		int a = tuplezz[0]; //Location of branch out. Maybe the counter example location. Have to check
		int b = tuplezz[1]; // Location of Branch in. Maybe the counter example location. Have to check
		m_Logger.warn(a);
		m_Logger.warn(b);
			
		return result;
	}

	private void computeFlowSensitiveTraceFormula(IPredicate errorPrecondition, IRun<CodeBlock, IPredicate> counterexampleRun,
		IPredicate falsePredicate, ModifiableGlobalVariableManager modGlobVarManager, SmtManager smtManager, ArrayList<int[]> informationFromCFG) 
	
	{
		NestedWord<CodeBlock> counterexampleWord = (NestedWord<CodeBlock>) counterexampleRun.getWord();
		
		m_Logger.warn(" * * * * ENTERED computerFlowSensitiveTraceFormula * * * * * ");
		DefaultTransFormulas nestedTransFormulas = new DefaultTransFormulas(counterexampleWord, errorPrecondition, falsePredicate, new TreeMap<>(), modGlobVarManager, false);
		NestedSsaBuilder ssaBuilder = new NestedSsaBuilder(counterexampleWord, smtManager, nestedTransFormulas, modGlobVarManager, m_Logger, false);
		NestedFormulas<Term, Term> ssa = ssaBuilder.getSsa();
		m_Logger.warn("Counter Example = " + ssa.getTrace().asList() ); //counter example in a list.
		m_Logger.warn("Precondition = " + ssa.getPrecondition());
		//m_Logger.warn("PRECONDITION --> " + precondition);
		int[] Branch_Information = informationFromCFG.get(0); // !!! CAUTION !!! JUST FOR ONE AT THE MOMENT _ _ !!! HARD CODED !!!
		int a = Branch_Information[0]; //Location of branch out. Maybe the counter example location. Have to check
		int b = Branch_Information[1]; // Location of Branch in. Maybe the counter example location. Have to check
		m_Logger.warn("Branch out at "+a);
		m_Logger.warn("Branch in at " + b);
		m_Logger.warn("- -");
		
		//////////////////////////////////////////// - - FORMULA WITH CONJUNCTS - - ////////////////////////////////////////
		ArrayList<Term> formulas_list = new ArrayList<Term>(); // initializing a new array list that will be later turned to conjuncts
		//formulas_list.add(Util.not(smtManager.getScript(), ssa.getPrecondition())); // adding the precondition in the array
		for(int k = 0; k < counterexampleWord.length(); k++)
		{
			formulas_list.add(ssa.getFormulaFromNonCallPos(k));
		}
		Term conjunct_formula = SmtUtils.and(smtManager.getScript(), formulas_list); //make conjuncts from a list of formulas.
		m_Logger.warn("CONJUNCTION OF COUNTER EXAMPLE = " + conjunct_formula);
		//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
		m_Logger.warn("Location check 1 for debugging");
		
		//////////////////////////////////////////- - FORMULA WITH IMPLICATIONS - - ////////////////////////////
		Term right_side;
		Term implication_formula = Util.implies(smtManager.getScript(), ssa.getFormulaFromNonCallPos(0)); //First line in the program
		//Term implication_formula = Util.implies(smtManager.getScript(), Util.not(smtManager.getScript(), ssa.getPrecondition())); // adding precondition as the first formula
		for(int k = 1; k < counterexampleWord.length()-1; k++)
		{
			right_side = ssa.getFormulaFromNonCallPos(k); // Formula that will be put on the right side of the implication
			implication_formula = Util.implies(smtManager.getScript(), implication_formula, right_side); 
		}
		m_Logger.warn("IMPLICATION FORMULA OF COUNTER EXAMPLE = " + implication_formula);
		//////////////////////////////////////////////////////////////////////////////////////////////////////////	
		m_Logger.warn("Location check 2 for debugging");
		
		
		
		//////////////////////////////////////// - - - Pro-Flow Sensitive Formula //////////////////////////////////
		
		// Markhor-formula:: ( guard(branch) IMPLIES branch AND neg( guard(branch) ) IMPLIES all variables remain the same )
		// The problem is how to use markhor formula.
		
		
		
		

		CodeBlock statement1 = counterexampleWord.getSymbolAt(0); // y=0
		CodeBlock statement2 = counterexampleWord.getSymbolAt(1); // assume(y==0)
		CodeBlock statement3 = counterexampleWord.getSymbolAt(2); // y==1
		TransFormula transition_formula1 = statement1.getTransitionFormula();
		TransFormula transition_formula2 = statement2.getTransitionFormula();
		TransFormula transition_formula3 = statement3.getTransitionFormula();
		
		TransFormula transition_formula4 = TransFormula.sequentialComposition(m_Logger, m_Services, smtManager.getBoogie2Smt(), false, false, false, transition_formula2,transition_formula1);
		TransFormula transition_formula5 = transition_formula3.sequentialComposition(m_Logger, m_Services, smtManager.getBoogie2Smt(), false, false, false, transition_formula4);
		
		
		
		//TransFormula markhor = TransFormula.computeMarkhorTransFormula(transition_formula, smtManager.getBoogie2Smt(), m_Services, m_Logger);
		
		m_Logger.warn("Location check 2.5 for debugging");

		
		////////////////////////////////////////////////////////////////////////////////////////////////////////////////
		
		/////////////////////////////////////// - - TRANSFORM INTO CONJUNCTIVE NORMAL FORM - - ////////
		Cnf cnf = new Cnf(smtManager.getScript(), m_Services , smtManager.getVariableManager());
		Term conjunctive_normal_form = cnf.transform(implication_formula); //Term is a formula 
		Term[] conjunt_array = SmtUtils.getConjuncts(conjunctive_normal_form);
		m_Logger.warn("CONJUNCTS IN CNF = " + conjunt_array);
		//////////////////////////////////////////////////////////////////////////////////////////////
		
		
		
		
		// We also have to do a mapping, which maps each formula to each statement in the program.
		m_Logger.warn("Locationcheck 3 for debugging");
		
		

//		smtManager.getScript().push(1);
//		Term precondition = ssa.getPrecondition();
//		m_Logger.warn(precondition);
//		String name = "Pre-condition";
//		Annotation annot = new Annotation(":named", name);
//		Term annotTerm = smtManager.getScript().annotate(precondition, annot);
//		smtManager.assertTerm(annotTerm);
//		
//		
//		Term term;
//		for(int i=0; i< counterexample.length(); i++)
//		{
//			term = ssa.getFormulaFromNonCallPos(i); //Should we now get term from the conjunct ??
//			name = "Formula" + i;
//			annot = new Annotation(":named", name);
//			annotTerm = smtManager.getScript().annotate(term, annot);
//			smtManager.assertTerm(annotTerm);
//			m_Logger.warn(term.toString());
//		}
//		LBool sat = smtManager.getScript().checkSat();
//		m_Logger.warn("LBOOL");
//		
//		Term[] unsat_core = smtManager.getScript().getUnsatCore();
//		m_Logger.warn("LBOOL");
		// Big conjunct -> annotate each term in that conjunct -> feed it to the SMT solver

		

		smtManager.getScript().push(1);
		Term precondition = Util.not(smtManager.getScript(), ssa.getPrecondition()); // FEEDING THE COMPLIMENT OF THE PRECONDITION
	//	precondition = Util.not(smtManager.getScript(), ssa.getPrecondition()); 
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
			m_Logger.warn(term.toString());
		}
		
		Term neg_post_cond = ssa.getFormulaFromNonCallPos(counterexampleWord.length()-1);
		name = "post-condition";
		annot = new Annotation(":named", name);
		annotTerm = smtManager.getScript().annotate(Util.not(smtManager.getScript(),neg_post_cond ), annot);
		smtManager.assertTerm(annotTerm);
		
		
		LBool sat = smtManager.getScript().checkSat();
		
		
		
		m_Logger.warn(sat);
		m_Logger.warn("LBOOL"); 
		 
		
		Term[] unsat_core = smtManager.getScript().getUnsatCore();
		m_Logger.warn("LBOOL");
		
		
		m_Logger.warn(ssaBuilder.toString());
		
	}

	private IPredicate computeErrorPrecondition(NestedWord<CodeBlock> counterexample, SmtManager smtManager,
			PredicateUnifier predicateUnifier, ModifiableGlobalVariableManager modGlobVarManager,ArrayList<int[]> informationFromCFG)
	{
		m_Logger.warn("* * * ENTERED COMPUTE ERROR PRECONDITION * * * *");
		PredicateTransformer pt = new PredicateTransformer(smtManager, modGlobVarManager, m_Services);
		int[] Branch_Information = informationFromCFG.get(0); // !!! CAUTION !!! JUST FOR ONE AT THE MOMENT _ _ !!! HARD CODED !!!
		int aa = Branch_Information[0]; //Location of branch out.
		int bb = Branch_Information[1]; // Location of Branch in.
		m_Logger.warn("Branch out at "+aa);
		m_Logger.warn("Branch in at " + bb);		
		// iterate over the counterexample and compute the error precondition
		//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
		//CodeBlock statement1 = counterexample.getSymbolAt(0);
		//TransFormula TranFormula = statement1.getTransitionFormula();
		//IPredicate post_condition = smtManager.newFalsePredicate();  //ERROR IF SET TO FALSE
		//IPredicate weakest_preconditionn = pt.weakestPrecondition(post_condition, TranFormula);
		//m_Logger.warn(weakest_preconditionn.toString());
		////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
		
		// Make an ArrayList of Transformulas in a backward fashion. 
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
							false, false, false, transition_formula ,combined_transition_formula);	
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
		m_Logger.warn("* * Entered findPathInCFG * *");
		m_Logger.warn(" ");
		
		try 
		{
			return (new IsEmpty<CodeBlock, IPredicate>(m_Services, cfg, 
					Collections.singleton(startPoint), possibleEndPoints)).getNestedRun();
		} 
		
		catch (OperationCanceledException e) 
		{
			m_Logger.warn("NO BRANCH FOUND !");
			throw new ToolchainCanceledException(getClass());
		}
	}
	
}