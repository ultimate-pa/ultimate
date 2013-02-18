/**
 *
 */
package local.stalin.plugins.safetychecker;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

import local.stalin.SMTInterface.SMTInterface;
import local.stalin.access.IUnmanagedObserver;
import local.stalin.access.WalkerOptions;
import local.stalin.boogie.cfgreducer.CFGEdge;
import local.stalin.boogie.cfgreducer.CFGExplicitNode;
import local.stalin.boogie.cfgreducer.SMTEdgeAnnotations;
import local.stalin.boogie.cfgreducer.SMTNodeAnnotations;
import local.stalin.core.api.StalinServices;
import local.stalin.logic.Formula;
import local.stalin.logic.FormulaUnFleterer;
import local.stalin.logic.FormulaWalker;
import local.stalin.logic.FunctionSymbol;
import local.stalin.logic.Sort;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;
import local.stalin.model.IEdge;
import local.stalin.model.IElement;
import local.stalin.model.INode;
import local.stalin.plugins.ResultNotifier;
import local.stalin.plugins.safetychecker.preferences.PreferenceValues;

/**
 * This class is the safety-checker, which goes depth first through the reduced CFG of the Boogie PL file and checks all possible paths for feasibility.
 * 
 */

public class SafetyCheckerObserver implements IUnmanagedObserver {
	
	protected static Logger 	s_Logger 					= StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	private CFGExplicitNode		m_Graphroot 				= null;
	private ArrayList<IElement> m_ShortestPath 				= new ArrayList<IElement>();
	private SMTInterface 		m_SMTInterface 				= null;
	private Theory 				m_Theory 					= null;
	private int					ctr							= 0;
	HashMap<String, Term>		m_OutConstants				= new HashMap<String, Term>();
	HashMap<Term, String>		m_ConstantsToVariableName	= new HashMap<Term, String>();
	private ArrayList<IEdge>	m_searchStack				= new ArrayList<IEdge>();
	private int					m_checkedPaths				= 0;
	private long				m_totalTime					= 0;
	
	
	@Override
	public boolean process(IElement root) {
		ctr 			= 0;
		m_checkedPaths = 0;
		m_totalTime = 0;
		m_Graphroot		= (CFGExplicitNode)root;
		
		m_Theory		= m_Graphroot.getTheory();
		//m_SMTInterface  = (SMTInterface)StalinServices.getInstance().getStoredObject("solver");
//		m_SMTInterface = new SMTInterface(m_Theory, SMTInterface.SOLVER_GROUNDIFY);
//		StalinServices.getInstance().putInToolchainStore("groundifier", m_SMTInterface);
		m_SMTInterface = (SMTInterface)StalinServices.getInstance().getStoredObject("groundifier");
		if (m_SMTInterface == null)
			s_Logger.debug("StalinServices failed to store solver object!");
		
		ConfigurationScope scope = new ConfigurationScope();
		IEclipsePreferences prefs = scope.getNode(Activator.PLUGIN_ID);
		
		int maxStepNumber = prefs.getInt(PreferenceValues.NAME_MAXSTEPNUMBER, PreferenceValues.VALUE_MAXSTEPNUMBER_DEFAULT);
		while (true){
			if (m_checkedPaths>=maxStepNumber){
				//s_Logger.info("Safety Checker quit with no result after " + step + " steps!");
				break;
			}
			//Checks if there is a new shortest path to an error location...
			if (!searchShortestPath_BFS()) {
				//if not then checking is finished and program proved to be correct
				ResultNotifier.programCorrect();
				break;
			} else if(m_ShortestPath.size() < 2) {
				s_Logger.info(m_ShortestPath.toString() + " is a real counterexample!");
				ResultNotifier.programIncorrect();
				break;
			}

			//... else check new shortest path...
			s_Logger.info("Checking " + m_ShortestPath.toString());
			//step++;
			if (checkShortestPath()){
				s_Logger.info("Check succeeded for path " + m_ShortestPath.toString());
				//if path is unsatisfiable and ...

				if (!splitPathByInterpolants()){
					s_Logger.info("SMT solver returned an error message!");
					break;
				}
				//shortest path must be empty for the function searchShortestPath to find a new one
				clearForNextRun();
			} else {
				s_Logger.info("Check failed for path " + m_ShortestPath.toString());
				//program is incorrect, stop the machinery, result notifier already called in function checkShortestPath()
				break;
			}
			//break;
		}
		s_Logger.info("Safety Checker quit after " + m_checkedPaths + " steps" + (m_checkedPaths>=maxStepNumber? " with no result!":"!"));
		
		s_Logger.info("BMdata:(Safety Checker) >(5)PC#: " + m_checkedPaths);
		s_Logger.info("BMdata:(Safety Checker) >(6)TIME#: " + m_totalTime);
		
		m_checkedPaths = 0;
		m_totalTime = 0;
		
		int edgeChecks = ((CFGEdge)m_Graphroot.getOutgoingEdges().get(0)).getTheoremProverCount();
		long edgeChecksTime = ((CFGEdge)m_Graphroot.getOutgoingEdges().get(0)).getTotalTime();
		
		s_Logger.info("BMdata:(Edge Checks) >(7)EC#: " + edgeChecks);
		s_Logger.info("BMdata:(Edge Checks) >(8)TIME#: " + edgeChecksTime);
		
		((CFGEdge)m_Graphroot.getOutgoingEdges().get(0)).resetStats();

		return false;
	}	

	private void clearForNextRun(){
		m_ShortestPath.clear();
		m_OutConstants.clear();
	}
	
	// alternative search with BFS
	private boolean searchShortestPath_BFS() {
		m_searchStack.clear();
		for (IEdge e: m_Graphroot.getOutgoingEdges()) {
			m_searchStack.add(e);
			if (e.getTarget().getPayload().getName().contains("ERROR")){
				buildErrorPath(0);
				return true;
			}
		}
		
		int i = 0;
		// if the search stack still holds edges that might lead to an error continue...
		while(i < m_searchStack.size()) {
			// get the current node which will be expanded
			
			INode node = m_searchStack.get(i).getTarget();
			// run through all descendants... 
			for(IEdge e: node.getOutgoingEdges()) {
				INode target = e.getTarget();
				// check if descendant has already been visited by another path(shorter path by construction of BFS)
				if (getNodeFromSearchStack(target)  < 0) {
					// append new edge to search stack since descendant has not been visited yet
					m_searchStack.add(e);
					// check if descendant is an error node
					if (target.getPayload().getName().contains("ERROR")) {
						buildErrorPath(m_searchStack.indexOf(e));
						return true;
					}
				}
			}
			i++;
		}
		return false;
	}
	
	// builds the error path by backtracking through search stack
	private void buildErrorPath(int errorIndex) {
		int i = errorIndex;
		while (i >= 0){ 
			IEdge e = m_searchStack.get(i);
			m_ShortestPath.add(0, e.getTarget());
			m_ShortestPath.add(0, e);
			i = getNodeFromSearchStack(e.getSource());
		}
		m_ShortestPath.add(0, m_Graphroot);
	}
	
	// returns the index of the edge in the search stack that leads to the node else returns -1
	private int getNodeFromSearchStack(INode node) {
		for (IEdge e: m_searchStack) {
			if (e.getTarget() == node) {
				return m_searchStack.indexOf(e);
			}
		}
		return -1;
	}
	
	//returns true if path is unsatisfiable
	private boolean checkShortestPath() {
		//Checking whether shortest path has any nodes with self-loops; this is set by function searchShortestPath()

		/*shortest path has at least one self-looping node and therefore must be separated to node-edge pairs
		 * in order to gain interpolants for splitting which is done by function getFormulas()*/
		//getting separated formulas from getFormulas()
		Formula[] formulas = getFormulas();
		//dumps formula to a designated file
		dumpFormula(formulas);
		
		//getting interpolants from SMT interface
		long startTime = System.currentTimeMillis();
		Formula[] interpolants = m_SMTInterface.computeInterpolants(formulas, null);
		m_totalTime += (System.currentTimeMillis() - startTime);
		m_checkedPaths++;
		
		//Check if SMT interface returned valid result ...
		if (interpolants == null){
			//SMT interface proved formula to be satisfiable and therefore path is a real counterexample
			s_Logger.info(m_ShortestPath.toString() + " is a real counterexample!");
			ResultNotifier.programIncorrect();
			return false;
		}

		//add newly obtained interpolants to the payload of the corresponding nodes because they will be needed explicitly for splitting
	
		for (int i = 4; i < m_ShortestPath.size()-2; i+=2){
			CFGExplicitNode node = (CFGExplicitNode)m_ShortestPath.get(i);
			SCNodeAnnotations scAnnotations = (SCNodeAnnotations)node.getPayload().getAnnotations().get("SC");
			if (scAnnotations == null){
				scAnnotations = new SCNodeAnnotations();
				node.getPayload().getAnnotations().put("SC", scAnnotations);
			}
			Formula tmp_interpolant = interpolants[i/2-2];
			// reverts all substitute variables of the interpolant to the correct variables of the specific node
			ConstToVariableVisitor ctvVisitor = new ConstToVariableVisitor(scAnnotations.getConstants(),
					m_ConstantsToVariableName, node, m_Theory);
			FormulaWalker formulaWalker = new FormulaWalker(ctvVisitor, m_Theory);
			Formula interpolant = formulaWalker.process(tmp_interpolant);
			Formula invariant = null;
			//get old invariant of this node
			Formula old_invariant = scAnnotations.getInvariant();
			//Check if there was an old invariant ...
			if (old_invariant == null){
				//no old invariant found, therefore new interpolant is first invariant of this node
				invariant = interpolant;
			} else {
				//old invariant found, therefore appending new interpolant to old invariant by conjunction
				invariant = m_Theory.and(interpolant, old_invariant);
			}
			//putting new interpolant and invariant in payload of node
			scAnnotations.setInvariant(invariant);
			scAnnotations.setInterpolant(interpolant);
		}
		return true;
	}

	//returns an array of the formulas corresponding to the current shortest path
	@SuppressWarnings("unchecked")
	private Formula[] getFormulas(){
		ArrayList<Formula> tmp_formulas = new ArrayList<Formula>();
		//get all global variables from procedure entry node
		//If node holds any old variables then...
		
		//path has self-loops and therefore must be separated in pairs of node and outgoing edge
		m_OutConstants = new HashMap<String, Term>();
		
		CFGExplicitNode procEntry = (CFGExplicitNode)m_ShortestPath.get(2);
		HashMap<TermVariable, Term> global_variables = new HashMap<TermVariable, Term>();
		HashMap<String, TermVariable> old_vars = (HashMap<String, TermVariable>)procEntry.getSMTAnnotations().getAnnotationsAsMap().get("oldvars");
		if (old_vars != null) {
			for (TermVariable global_tv: old_vars.values()){
				global_variables.put(global_tv, makeConstant(global_tv));
			}
			//filling up out_constants
			for(String vname: old_vars.keySet()){
				m_OutConstants.put(vname, global_variables.get(old_vars.get(vname)));
			}
		}
		/*iterates through shortest path from node to node until reaching last node with outgoing edge
		 * and collects formulas in array tmp_formulas;
		 * starts at the procedure node and not the root node*/
		for (int i = 2; i < m_ShortestPath.size(); i+=2){
			Formula tmp_formula = get_partialFormula(i);
			//Adds all global variables to the formula
			for (TermVariable global_tv: global_variables.keySet()){
				tmp_formula = m_Theory.let(global_tv, global_variables.get(global_tv), tmp_formula);
			}
			tmp_formulas.add(tmp_formula);
		}
		//putting list in an array and return that array
		Formula[] formulas = new Formula[tmp_formulas.size()];
		return tmp_formulas.toArray(formulas);
	}
	
	//builds and returns the formula for a i'th node and its succeeding edge on the current path
	private Formula get_partialFormula(int i){
		//will hold the resulting formula
		Formula formula = null;
		//will hold the out going variables of the edge if node is not end of path
		HashMap<String, TermVariable> outgoingVariablesOfEdge = null;
		HashSet<TermVariable> variablesOfEdge = null;
		
		CFGExplicitNode		node				= (CFGExplicitNode)m_ShortestPath.get(i);
		SMTNodeAnnotations	smtNodeAnnotations	= node.getSMTAnnotations();
		CFGEdge 			edge 				= null;
		SMTEdgeAnnotations	smtEdgeAnnotations	= new SMTEdgeAnnotations();
		
		//getting the incoming variables of the node
		HashMap<String, TermVariable>	incomingVariablesOfNode	= smtNodeAnnotations.getInVars();
		HashSet<TermVariable> 			variablesOfNode 		= smtNodeAnnotations.getVars();
		HashSet<TermVariable>			newVariables			= new HashSet<TermVariable>();
		newVariables.addAll(variablesOfNode);
		//HashMap that store all let-statements of this node's variables that are mapped to a constant
		HashMap<Term, TermVariable> allLetStatementsOfNode		= new HashMap<Term, TermVariable>();
		HashMap<Term, TermVariable> allIncomingConstantsOfNode	= new HashMap<Term, TermVariable>();
		//getting the formula of the node(assertion)
		Formula assertion = (Formula)smtNodeAnnotations.getAssertion();
		
		//Check if node is end of path ...
		if (i < m_ShortestPath.size()-1){
			//node is not the end of the path
			edge = (CFGEdge)m_ShortestPath.get(i+1);
			smtEdgeAnnotations = edge.getSMTAnnotations();
			//getting the outgoing variables of the edge
			HashMap<String, TermVariable> incomingVariablesOfEdge = smtEdgeAnnotations.getInVars();
			outgoingVariablesOfEdge = smtEdgeAnnotations.getOutVars();
			variablesOfEdge = smtEdgeAnnotations.getVars();
			//add node and edge variables to n_vars
			newVariables.addAll(variablesOfEdge);
			//getting the formula of the edge(assumption)
			Formula assumption = smtEdgeAnnotations.getAssumption();
			//building new formula but yet without mapping of in- and outgoing variables
			formula = m_Theory.and(assertion, assumption);
			for(String vname: incomingVariablesOfEdge.keySet()){
				//if a outgoing constant has been declared for this incoming variable of the node then ...
				if (!m_OutConstants.keySet().contains(vname)){
					//s_Logger.debug("This incoming variable " + vname + ": " + incomingVariablesOfEdge.get(vname).toString() + " of the node " + m_ShortestPath.get(i) +
					//		" has not been declared anywhere on the path \n" + m_ShortestPath.toString());
					m_OutConstants.put(vname, makeConstant(incomingVariablesOfEdge.get(vname)));
				}
				TermVariable in_var = incomingVariablesOfEdge.get(vname);
				Term const_Term = m_OutConstants.get(vname);
				formula = m_Theory.let(in_var, const_Term, formula);
				allLetStatementsOfNode.put(const_Term, in_var);
				newVariables.remove(in_var);
			}
		} else {
			//node is end of path
			formula = assertion;
		}
		//iterating through all incoming variables of the node/edge
		for(String vname: incomingVariablesOfNode.keySet()){
			//if a outgoing constant has been declared for this incoming variable of the node then ...
			if (!m_OutConstants.keySet().contains(vname)){
				s_Logger.debug("This incoming variable " + vname + ": " + incomingVariablesOfNode.get(vname).toString() + " of the node " + m_ShortestPath.get(i) +
						" has not been declared anywhere on the path \n" + m_ShortestPath.toString());
				m_OutConstants.put(vname, makeConstant(incomingVariablesOfNode.get(vname)));
			}
			TermVariable in_var = incomingVariablesOfNode.get(vname);
			Term const_Term = m_OutConstants.get(vname);
			formula = m_Theory.let(in_var, const_Term, formula);
			allIncomingConstantsOfNode.put(const_Term, in_var);
			allLetStatementsOfNode.put(const_Term, in_var);
			newVariables.remove(in_var);
		}
		//make new constants only if there exists an outgoing edge
		if (edge != null){
			//get the incoming variables of the edge
			HashMap<String, TermVariable> in_vars_edge = smtEdgeAnnotations.getInVars();
			//iterating through all outgoing variables of the edge in order to declare constants and add them to out_constants
			for (String vname: outgoingVariablesOfEdge.keySet()){
				//check if this outgoing variable has really been changed or not
				if (in_vars_edge.containsValue(outgoingVariablesOfEdge.get(vname))){
					//if variable is also incoming variable then skip it
					continue;
				}
				//create new constant term for variable
				Term const_Term = makeConstant(outgoingVariablesOfEdge.get(vname));
				//map new constant to variable name
				m_OutConstants.put(vname, const_Term);
				//map out going variable to new constant
				TermVariable out_var = outgoingVariablesOfEdge.get(vname);
				formula = m_Theory.let(out_var, const_Term, formula);
				allLetStatementsOfNode.put(const_Term, out_var);
				newVariables.remove(out_var);
			}
		}
		//Check all remaining variables of the node which are not in or out variables
		for (TermVariable var: newVariables){
			Term const_Term = makeConstant(var);
			formula = m_Theory.let(var, const_Term, formula);
			allLetStatementsOfNode.put(const_Term, var);
		}
		SCNodeAnnotations scAnnotations = (SCNodeAnnotations)node.getPayload().getAnnotations().get("SC");
		if (scAnnotations == null){
			scAnnotations = new SCNodeAnnotations();
			node.getPayload().getAnnotations().put("SC", scAnnotations);
		}
		scAnnotations.m_constants = allLetStatementsOfNode;
		return formula;
	}

	/*returns new constant for variable or
	 * returns constant that has already been created for this variable before
	 */
	private Term makeConstant(TermVariable tv){
		//new name for constant variable
		String constName = tv.getName() + "_const";
		//need a list of sorts of the input parameters of the function
		Sort[] dummy_Sorts = {};
		/*faking constant by creating function without input parameters and getting function symbol of newly created fake constant or
		 * of old fake constant that has already been created before*/
		FunctionSymbol fsym = m_Theory.getFunction(constName, dummy_Sorts);
		if (fsym == null)
			fsym = m_Theory.createFunction(constName, dummy_Sorts, tv.getSort());
		//need list of terms for input parameters of function in order to create term out of it
		Term[] dummyTerms = {};
		//making constant term and returning it
		Term const_Term = m_Theory.term(fsym, dummyTerms);
//		const_to_Variable.put(const_Term, tv);
		m_ConstantsToVariableName.put(const_Term, tv.getName());
		return const_Term;
	}
	
	//splits all inner nodes on the path and extends their assertions with corresponding interpolants
	private boolean splitPathByInterpolants(){
		boolean result = true;
		//iterates through all inner nodes of the path and splits them
		for (int i = 4; i < m_ShortestPath.size()-1; i += 2){
			//get assertion and interpolant of node
			CFGExplicitNode node = (CFGExplicitNode)m_ShortestPath.get(i);
			SCNodeAnnotations	scAnnotations		= (SCNodeAnnotations)node.getPayload().getAnnotations().get("SC");
			SMTNodeAnnotations	smtNodeAnnotations	= node.getSMTAnnotations();
			
			Formula assertion	= smtNodeAnnotations.getAssertion();
			Formula interpolant = scAnnotations.getInterpolant();
			//Create new node for splitting
			CFGExplicitNode		splitNode				= node.copyWithoutEdges();
			SMTNodeAnnotations	smtCopyNodeAnnotations	= splitNode.getSMTAnnotations();
			//append interpolant to the assertions
			smtNodeAnnotations.setAssertion(m_Theory.and(assertion, interpolant));
			smtCopyNodeAnnotations.setAssertion(m_Theory.and(assertion, m_Theory.not(interpolant)));
			//Run SSA on splitNodes annotation
			splitNode.getSMTAnnotations().useSSA();
			//copy all in- and outgoing edges of original node
			splitNode.copyAllPredecessorsFromNode(node);
			splitNode.copyAllSuccessorsFromNode(node);
			//this should be unnecessary because error-edge should be unsatisfiable anyway
			CFGEdge errorEdge = null;
			for (IEdge iedge: node.getOutgoingEdges()){
				if(iedge.getTarget().getPayload().getName().contains("ERROR")){
					errorEdge = (CFGEdge)iedge;
					break;
				}
			}
			if (errorEdge != null)
				errorEdge.deleteEdge();
			//delete all unsatisfiable edges of both nodes
			result = result && node.cleanUnsatisfiableEdges();
			splitNode.cleanUnsatisfiableEdges();
			
			//remove nodes that have no effect on the loops or the error paths anymore
			if (node.getOutgoingEdges().size() == 0) {
				node.removeAllIncoming();
			}
			if (splitNode.getOutgoingEdges().size() == 0) {
				splitNode.removeAllIncoming();
			}
		}
		return result;
	}
	
	//deletes the path as far as possible
	private void deleteShortestPath() {
		deletePath(m_ShortestPath);
	}
	
	//deletes the given path as far as possible
	private void deletePath(ArrayList<IElement> path){
		if (!(path.size() < 3)){
			CFGExplicitNode node = (CFGExplicitNode)path.get(path.size()-1);
			if (node.getOutgoingEdges().size() < 1){
				CFGEdge edge = (CFGEdge)path.get(path.size()-2);
				edge.deleteEdge();
				for(int i=0;i<2;i++){
					path.remove(path.size()-1);
				}
				this.deleteShortestPath();
			}
		}
		path.clear();
		return;
	}
	
	protected void dumpFormula(Formula[] formulas){
		ConfigurationScope scope = new ConfigurationScope();
		IEclipsePreferences prefs = scope.getNode(Activator.PLUGIN_ID);
		
		if (!prefs.getBoolean(PreferenceValues.NAME_ACTIVATEDUMPFORMULA, PreferenceValues.VALUE_ACTIVATEDUMPFORMULA_DEFAULT)){
			s_Logger.info("Did not dump interpolation problem to file!");
			return;
		}
		
		String s_intpol_filename = prefs.get(PreferenceValues.NAME_DUMPPATH, "C:") + "/intpol" + ctr + ".smt";
		File intpol_filename = new File(s_intpol_filename);
		FileWriter intpol_file;
		try {
			intpol_file = new FileWriter(intpol_filename);
			PrintWriter intpol_pw = new PrintWriter(intpol_file);
			FormulaUnFleterer unFleterer = new FormulaUnFleterer(m_Theory);
			for (int i = 0; i < formulas.length; i++) {
				String s_formula_filename = prefs.get(PreferenceValues.NAME_DUMPPATH, "C:") + "/intpol" + ctr + "_f" + i + ".smt";
				File formula_filename = new File(s_formula_filename);
				formulas[i] = unFleterer.unflet(formulas[i]);
				FileWriter formula_file;
				try {
					formula_file = new FileWriter(formula_filename);
					PrintWriter formula_pw = new PrintWriter(formula_file);
					
					SMT2File.writeFormulaToFile(formula_pw, formulas[i]);
					formula_file.close();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
			this.m_Theory.dumpInterpolationBenchmark(intpol_pw, formulas);
			intpol_file.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		s_Logger.info("Dumped interpolation problem in file" + s_intpol_filename + "!");
		ctr++;
	}
	
	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void init() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}
}
