package de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqSymbolTable;

public class InputDetSuccConstruction {
	private final Script mScript;
	private final ILogger mLogger;
	private final GuardGraph mGuardGraph;
	private final Set<GuardGraph> mSeenNodes;
	private final LinkedList<GuardGraph> mQueue;
	private final HashMap<String, Term> mMonomials;
	private final Sort mSort;
	
	
	public InputDetSuccConstruction(ILogger logger, GuardGraph powersetAuto, Script script, ReqSymbolTable symboltable) {
		mLogger = logger;
		mScript = script;
		//mGuardGraph = constructInputDetSuccAutomaton(powersetAuto, symboltable.getInputVars());
		mGuardGraph = new GuardGraph(0);
		mSeenNodes = new HashSet<GuardGraph>();
		mQueue = new LinkedList<GuardGraph>();
		mSort = mScript.sort("Bool");
		mMonomials = createMonomials(symboltable);
		
		
		// TODO just for debug, remove later
		/*
		for (String key : mMonomials.keySet()) {
			mLogger.warn(String.format("Key %s has monomials %s", key, mMonomials.get(key)));
		}
		mLogger.warn(mMonomials.size());
		*/
	}
	
	// inputvar I : {Term I, Term notI}
	private HashMap<String, Set<Term>> inVarToTermMap(Set<String> inVars) {
		HashMap<String, Set<Term>> result = new HashMap<String, Set<Term>>();
		for (String varname : inVars) {
			Term a = mScript.variable(varname, mSort);
			Term na = SmtUtils.not(mScript, a);
			Set<Term> values = new HashSet<Term>();
			values.add(a);
			values.add(na);
			result.put(varname, values);
		}
		return result;
	}
	
	// HashMap<String, Term>
	// mon1 : I and J and ....
	private HashMap<String, Term> createMonomials(ReqSymbolTable sbt) {
		HashMap<String, Set<Term>> inVarToTerms = inVarToTermMap(sbt.getInputVars());
		HashMap<String, Term> result = new HashMap<String, Term>();
		HashMap<String, Term> oldRes = new HashMap<String, Term>();
		String monKey = "mon";
		
		int monIndex = 0;
		
		// get one key as first element to create the first monomials (length 1)
		// e.g. mon0 will be I and mon1 will be not I
		for (String key : inVarToTerms.keySet()) {
			for (Term boolInputVal : inVarToTerms.get(key)) {
				result.put(monKey+Integer.toString(monIndex), boolInputVal);
				monIndex++;
			}
			monIndex = 0;
			inVarToTerms.remove(key);
			oldRes = new HashMap<String, Term>(result);
			break;
		}
		
		// now for the rest of the input Terms
		if (!inVarToTerms.isEmpty()) {
			for (String key : inVarToTerms.keySet()) {
				result = new HashMap<String, Term>();
				for (Term boolInputVal : inVarToTerms.get(key)) {
					for (String oldMonKey : oldRes.keySet()) {
						result.put(monKey+Integer.toString(monIndex), 
								SmtUtils.and(mScript, boolInputVal, oldRes.get(oldMonKey)));
						monIndex++;
					}
				}
				oldRes = new HashMap<String, Term>(result); 
			}
		}
		return result;
	}

	public GuardGraph getAutomaton() {
		return mGuardGraph;
	}
	
	private void addToSeen(GuardGraph node) {
		mSeenNodes.add(node);
	}
	
	private void addToQueue(GuardGraph node) {
		mQueue.add(node);
	}

	// calculate the successors here
	private Set<GuardGraph> findSuccessors(GuardGraph givenNode, Term givenMonomial) {
		// TODO implement this
		return new HashSet<GuardGraph>();
	}
	
	private GuardGraph constructInputDetSuccAutomaton(GuardGraph psauto, Set<String> inpVars) {
		// take starting node
		
		GuardGraph fromNode = psauto;

		/*
		 * SmtUtils.checkSatTerm to test if term and monomial satisfiable
		 */
		// add it to queue
		addToQueue(fromNode);
		
		// create new starting node
		Set<GuardGraph> succ = new HashSet<GuardGraph>();
		succ.add(fromNode);
		
		GuardGraph startingNode = new GuardGraph(0);
		
		
		// now go over the queue
		/*while (!mQueue.isEmpty()) {
			GuardGraph thisNode = mQueue.pop();
			// look at each input monomial
			for (Term monomial : mMonomials) {
				// calculate successor Node with given monomial
				succ = findSuccessors(thisNode, monomial);
				GuardGraph goingToNode = new GuardGraph(0);
				
				thisNode.addOutgoingNode(goingToNode, monomial);
				// test if gointToNode already in queueueueueu oder seen
				addToQueue(goingToNode);
				succ = new HashSet<GuardGraph>();
			}
			addToSeen(thisNode);
		}*/
		return startingNode;
	}
	
	private boolean testPartOfConj(Term edge, Term monomial) {
		// if monomial is part of the edge conjunction return true; else false
		return false;
	}
}
