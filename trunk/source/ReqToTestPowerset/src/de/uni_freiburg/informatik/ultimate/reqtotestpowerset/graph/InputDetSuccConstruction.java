package de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class InputDetSuccConstruction {
	private final Script mScript;
	private final ILogger mLogger;
	private final GuardGraph mGuardGraph;
	private final Set<GuardGraph> mSeenNodes;
	private final LinkedList<GuardGraph> mQueue;
	private final Set<Term> mMonomials;
	
	
	public InputDetSuccConstruction(ILogger logger, GuardGraph powersetAuto, Script script, Set<String> inputVariables) {
		mLogger = logger;
		mScript = script;
		mGuardGraph = constructInputDetSuccAutomaton(powersetAuto, inputVariables);
		mSeenNodes = new HashSet<GuardGraph>();
		mQueue = new LinkedList<GuardGraph>();
		mMonomials = createMonomials(inputVariables);
	}
	
	// iterate over the input variables and create all the possible monomials
	// might be a good ideea to do this in another class altogether...
	private Set<Term> createMonomials(Set<String> inputVariables) {
		// TODO implement this
		return new HashSet<Term>();
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
		GuardGraph fromNode = psauto.getOutgoingNodes().get(0);
		// add it to queue
		addToQueue(fromNode);
		
		// create new starting node
		Set<GuardGraph> succ = new HashSet<GuardGraph>();
		succ.add(fromNode);
		
		GuardGraph startingNode = new GuardGraph(succ);
		GuardGraph thisNode = startingNode;
		
		// now go over the queue
		while (!mQueue.isEmpty()) {
			succ.clear();
			thisNode = mQueue.pop();
			// look at each input monomial
			for (Term monomial : mMonomials) {
				// calculate successor Node with given monomial
				succ = findSuccessors(thisNode, monomial);
				GuardGraph goingToNode = new GuardGraph(succ);
				
				thisNode.addOutgoingNode(goingToNode, monomial);
				
				addToQueue(goingToNode);
				succ.clear();
			}
			addToSeen(thisNode);
		}
		return startingNode;
	}
}
