package de.uni_freiburg.informatik.ultimate.modelcheckerutils.staticutils;

import java.rmi.UnexpectedException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SCNodeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTEdgeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTNodeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.VariableSSAManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers.SubstituteTermTransformer;
/*
 * This class takes a path of IElements as build by the safety checker plugin and returns an array of
 * formulas representing the path. It holds all information about the mapping of the constants to their
 * according variables.
 * That why this class should only be instantiated once as member attribute in order to hold the information
 * of the constants to variable mapping. It is not static through, because each run of the safety checker
 * should instantiate a fresh object of this class. 
 */
public class FormulaArrayBuilder {
	
	private Script mScript = null;
	private HashMap<BoogieVar, Term>	mInputVariables					= new HashMap<BoogieVar, Term>();
	private HashMap<BoogieVar, Term>	mOutConstants					= new HashMap<BoogieVar, Term>();
	private HashMap<Term, BoogieVar>	mConstantsToBoogieVariableMap	= new HashMap<Term, BoogieVar>();
	
	public FormulaArrayBuilder(Script script) {
		mScript = script;
	}
	
	//returns an array of the formulas corresponding to the current shortest path
	public Term[] getFormulas(ArrayList<IElement> shortestPath){
		ArrayList<Term> tmp_formulas = new ArrayList<Term>();
		//get all global variables from procedure entry node
		//If node holds any old variables then...
		
		//path has self-loops and therefore must be separated in pairs of node and outgoing edge
		mOutConstants = new HashMap<BoogieVar, Term>();
		mInputVariables = new HashMap<BoogieVar, Term>();
		
		/*iterates through shortest path from node to node until reaching last node with outgoing edge
		 * and collects formulas in array tmp_formulas;
		 * starts at the procedure node and not the root node*/
		for (int i = 2; i < shortestPath.size(); i+=2) {
			Term tmp_formula = getPartialFormula((CFGExplicitNode) shortestPath.get(i), 
					i < shortestPath.size()-1 ? (CFGEdge) shortestPath.get(i+1) : null);//i, shortestPath);
			//Adds all global variables to the formula
			
			tmp_formulas.add(tmp_formula);
		}
		//putting list in an array and return that array
		Term[] formulas = new Term[tmp_formulas.size()];
		return tmp_formulas.toArray(formulas);
	}
	
	//builds and returns the formula for a i'th node and its succeeding edge on the current path
	public Term getPartialFormula(CFGExplicitNode node, CFGEdge edge) {//int i, ArrayList<IElement> shortestPath) throws SMTLIBException{
		SubstituteTermTransformer subTermTransformer	= new SubstituteTermTransformer();
		HashMap<Term, Term> subTermMapping = new HashMap<Term, Term>();
		//will hold the resulting formula
		Term formula = null;
		//will hold the out going variables of the edge if node is not end of path
		HashMap<BoogieVar, TermVariable> outgoingVariablesOfEdge = null;
		HashSet<TermVariable> variablesOfEdge = null;
		
//		CFGExplicitNode		node				= (CFGExplicitNode)shortestPath.get(i);
		SMTNodeAnnotations	smtNodeAnnotations	= node.getSMTAnnotations();
//		CFGEdge 			edge 				= null;
		SMTEdgeAnnotations	smtEdgeAnnotations	= new SMTEdgeAnnotations();
		
		//getting the incoming variables of the node
		HashMap<BoogieVar, TermVariable> incomingVariablesOfNode	= smtNodeAnnotations.getInVars();
		HashSet<TermVariable> 			 variablesOfNode 			= smtNodeAnnotations.getVars();
		HashSet<TermVariable>			 newVariables				= new HashSet<TermVariable>();
		newVariables.addAll(variablesOfNode);
		//HashMap that store all let-statements of this node's variables that are mapped to a constant
		HashMap<Term, TermVariable> variable2ConstantMapping		= new HashMap<Term, TermVariable>();
		HashMap<Term, TermVariable> allIncomingConstantsOfNode	= new HashMap<Term, TermVariable>();
		//getting the formula of the node(assertion)
		Term assertion = smtNodeAnnotations.getAssertion();
		
		//Check if node is end of path ...
		if (edge != null) {//(i < shortestPath.size()-1){
			//node is not the end of the path
			//edge = (CFGEdge)shortestPath.get(i+1);
			smtEdgeAnnotations = edge.getSMTAnnotations();
			//getting the outgoing variables of the edge
			HashMap<BoogieVar, TermVariable> incomingVariablesOfEdge = smtEdgeAnnotations.getInVars();
			outgoingVariablesOfEdge = smtEdgeAnnotations.getOutVars();
			variablesOfEdge = smtEdgeAnnotations.getVars();
			//add node and edge variables to n_vars
			newVariables.addAll(variablesOfEdge);
			//getting the formula of the edge(assumption)
			Term assumption = smtEdgeAnnotations.getAssumption();
			//building new formula but yet without mapping of in- and outgoing variables
			formula = Util.and(mScript, assertion, assumption);
//			formula = assumption; // without assertion of nodes
			
			for(BoogieVar boogieVar: incomingVariablesOfEdge.keySet()){
				//if a outgoing constant has been declared for this incoming variable of the node then ...
				if (!mOutConstants.keySet().contains(boogieVar)){
					Term const_Term = VariableSSAManager.makeConstant(incomingVariablesOfEdge.get(boogieVar));
					mConstantsToBoogieVariableMap.put(const_Term, boogieVar);
					mOutConstants.put(boogieVar, const_Term);
				}
				TermVariable in_var = incomingVariablesOfEdge.get(boogieVar);
				Term const_Term = mOutConstants.get(boogieVar);
				
//				formula = subTermTransformer.substitute(formula, in_var, const_Term);
				subTermMapping.put(in_var, const_Term);
				//formula = m_Script.let(new TermVariable[]{in_var}, new Term[]{const_Term}, formula);
				variable2ConstantMapping.put(const_Term, in_var);
				newVariables.remove(in_var);
			}
			formula = subTermTransformer.substitute(formula, subTermMapping);
			subTermMapping.clear();
		} else {
			//node is end of path
			formula = assertion;
		}
		//iterating through all incoming variables of the node/edge
		for(BoogieVar boogieVar: incomingVariablesOfNode.keySet()){
			//if a outgoing constant has been declared for this incoming variable of the node then ...
			if (!mOutConstants.keySet().contains(boogieVar)){
				// since this boogieVar is not a local variable it must be global variable. If it's not, throw an exception
				//TODO condition should use boogieVar.isOldvar() but somehow that doesn't work.
				Term const_Term = VariableSSAManager.makeConstant(incomingVariablesOfNode.get(boogieVar));
				mConstantsToBoogieVariableMap.put(const_Term, boogieVar);
				mOutConstants.put(boogieVar, const_Term);
				mInputVariables.put(boogieVar, const_Term);
			}
			TermVariable in_var = incomingVariablesOfNode.get(boogieVar);
			Term const_Term = mOutConstants.get(boogieVar);
			subTermMapping.put(in_var, const_Term);
//			formula = subTermTransformer.substitute(formula, in_var, const_Term);
			allIncomingConstantsOfNode.put(const_Term, in_var);
			variable2ConstantMapping.put(const_Term, in_var);
			newVariables.remove(in_var);
		}
		formula = subTermTransformer.substitute(formula, subTermMapping);
		subTermMapping.clear();
		
		//make new constants only if there exists an outgoing edge
		if (edge != null){
			//get the incoming variables of the edge
			HashMap<BoogieVar, TermVariable> in_vars_edge = smtEdgeAnnotations.getInVars();
			//iterating through all outgoing variables of the edge in order to declare constants and add them to out_constants
			for (BoogieVar boogieVar: outgoingVariablesOfEdge.keySet()){
				//check if this outgoing variable has really been changed or not
				if (in_vars_edge.containsValue(outgoingVariablesOfEdge.get(boogieVar))){
					//if variable is also incoming variable then skip it
					continue;
				}
				//create new constant term for variable
				Term const_Term = VariableSSAManager.makeConstant(outgoingVariablesOfEdge.get(boogieVar));
				mConstantsToBoogieVariableMap.put(const_Term, boogieVar);
				//map new constant to variable name
				mOutConstants.put(boogieVar, const_Term);
				//map out going variable to new constant
				TermVariable out_var = outgoingVariablesOfEdge.get(boogieVar);
				subTermMapping.put(out_var, const_Term);
//				formula = subTermTransformer.substitute(formula, out_var, const_Term);
//				formula = m_Script.let(new TermVariable[]{out_var}, new Term[]{const_Term}, formula);
				variable2ConstantMapping.put(const_Term, out_var);
				newVariables.remove(out_var);
			}
			formula = subTermTransformer.substitute(formula, subTermMapping);
			subTermMapping.clear();
		}
		//Check all remaining variables of the node which are not in or out variables
		for (TermVariable var: newVariables){
			Term const_Term = VariableSSAManager.makeConstant(var);
			subTermMapping.put(var, const_Term);
//			formula = subTermTransformer.substitute(formula, var, const_Term);
//			formula = m_Script.let(new TermVariable[]{var}, new Term[]{const_Term}, formula);
			variable2ConstantMapping.put(const_Term, var);
		}
		formula = subTermTransformer.substitute(formula, subTermMapping);
		subTermMapping.clear();
		
		SCNodeAnnotations scAnnotations = (SCNodeAnnotations)node.getPayload().getAnnotations().get("SC");
		if (scAnnotations == null){
			scAnnotations = new SCNodeAnnotations(mScript.term("true"));
			node.getPayload().getAnnotations().put("SC", scAnnotations);
		}
		scAnnotations.setConstants(variable2ConstantMapping);
		if(formula.getFreeVars().length > 0) {
			Logger.getLogger(Activator.s_PLUGIN_ID).warn("Partial formulas are not allowed to " +
					"contain free varaibles. This will cause a SMTLIBException.");
		}
		return formula;
	}
	public HashMap<BoogieVar, Term>	getOutConstants() {
		if(mOutConstants == null)
			throw new NullPointerException("Prior getFormula not called or failed!");
		return mOutConstants;
	}
	public HashMap<Term, BoogieVar>	getConstantsToBoogieVariableMap() {
		if(mConstantsToBoogieVariableMap == null)
			throw new NullPointerException("Prior getFormula not called or failed!");
		return mConstantsToBoogieVariableMap;
	}
	public HashMap<BoogieVar, Term>	getInputVariables() {
		if(mInputVariables == null)
			throw new NullPointerException("Prior getFormula not called or failed!");
		return mInputVariables;
	}
}
