package de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph;

import java.util.Collection;
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
	private Set<GuardGraph> mSeenNodes;
	private LinkedList<GuardGraph> mQueue;
	private final Set<Term> mMonomials;
	private final Sort mSort;
	private Set<GuardGraph> mAutStates;
	//TODO remove this hack later
	private Term mF = null;;
	
	
	public InputDetSuccConstruction(ILogger logger, GuardGraph powersetAuto, Script script, ReqSymbolTable symboltable) {
		mLogger = logger;
		mScript = script;
		mSeenNodes = new HashSet<GuardGraph>();
		mQueue = new LinkedList<GuardGraph>();
		mAutStates = new HashSet<>();
		mSort = mScript.sort("Bool");
		mMonomials = createMonomials(symboltable);

		mGuardGraph = constructInputDetSuccAutomaton(powersetAuto);
		
		String meh = "string";
//		Set<String> s1 = new HashSet<>();
//		s1.add(meh);
//		Set<String> s2 = new HashSet<>();
//		s2.add(meh);
//		
//		mLogger.warn(s1.contains(s2));
//		
//		mLogger.warn(s1.equals(s2));
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
			if (mF == null ) {
				mF = SmtUtils.and(mScript, a, na);
			}
			result.put(varname, values);
		}
		return result;
	}
	
	// HashMap<String, Term>
	// mon1 : I and J and ....
	private Set<Term> createMonomials(ReqSymbolTable sbt) {
		HashMap<String, Set<Term>> inVarToTerms = inVarToTermMap(sbt.getInputVars());
		Set<Term> result = new HashSet<>();
		Set<Term> oldRes = new HashSet<>();
		
		// get one key as first element to create the first monomials (length 1)
		// e.g. mon0 will be I and mon1 will be not I
		for (String key : inVarToTerms.keySet()) {
			for (Term boolInputVal : inVarToTerms.get(key)) {
				result.add(boolInputVal);
			}
			inVarToTerms.remove(key);
			oldRes = new HashSet<>(result);
			break;
		}
		
		// now for the rest of the input Terms
		if (!inVarToTerms.isEmpty()) {
			for (String key : inVarToTerms.keySet()) {
				result = new HashSet<>();
				for (Term boolInputVal : inVarToTerms.get(key)) {
					for (Term oldMonKey : oldRes) {
						result.add(SmtUtils.and(mScript, boolInputVal, oldMonKey));
					}
				}
				oldRes = new HashSet<>(result); 
			}
		}
		return result;
	}

	public GuardGraph getAutomaton() {
		return mGuardGraph;
	}

	// calculate the successors here
	private Set<GuardGraph> findSuccessors(GuardGraph givenNode, Term givenMonomial) {
		Set<GuardGraph> result = new HashSet<>();
		
		for (GuardGraph neighbour : givenNode.getOutgoingNodes()) {
			if (!(givenNode.getOutgoingEdgeLabel(neighbour) == null)) {
				if (!SmtUtils.isFalse(SmtUtils.and(mScript, givenNode.getOutgoingEdgeLabel(neighbour), givenMonomial))) {
					result.add(neighbour);
				}
			}
		}
		return result;
	}
	
	private GuardGraph collectionContains(Collection<GuardGraph> collection, GuardGraph thisInpDetANode) {
		for(GuardGraph gg: collection) {
			if(gg.isSameNode(thisInpDetANode)) {
				return gg;
			}
		}
		return null;
	}
	
	private GuardGraph constructInputDetSuccAutomaton(GuardGraph productAutomaton) {
		Set<GuardGraph> initialIndex = new HashSet<>();
		initialIndex.add(productAutomaton);
		GuardGraph initialPowerNode = new GuardGraph(0, new HashSet<GuardGraph>(initialIndex));
		mAutStates.add(initialPowerNode);
		int newlabel = 1;
		// add it to queue
		mQueue.add(initialPowerNode);
		
		// now go over the queue
		while (mQueue.size() > 0) {
		
			GuardGraph thisInpDetANode = mQueue.pop();
			mSeenNodes.add(thisInpDetANode);

			for (Term mon : mMonomials) {
				Set<GuardGraph> succsrs = new HashSet<>();
				for (GuardGraph buildingNode : thisInpDetANode.getBuildingNodes()) {
					succsrs.addAll(findSuccessors(buildingNode, mon));
				}
				GuardGraph targetNode = new GuardGraph(newlabel, succsrs);
				//TODO: refactor! take HashMap<set<GuardGraph>, GuardGraph> which stores the internal nodes i.e. succsrs and indexes nodes 
				// accordingly.
				if(collectionContains(mAutStates, targetNode) == null) {
					mAutStates.add(targetNode);
				} else {
					targetNode = collectionContains(mAutStates, targetNode);
				}
				
				// TODO this hack here seems stupid
				Term edgelabel = mF;
				for (GuardGraph fromNode : thisInpDetANode.getBuildingNodes()) {
					for (GuardGraph toNode : succsrs) {
						Term eh = SmtUtils.and(mScript, fromNode.getOutgoingEdgeLabel(toNode), mon);
						edgelabel = SmtUtils.or(mScript, edgelabel, eh);
					}	
				}
				if(collectionContains(mQueue, targetNode) == null && collectionContains(mSeenNodes, targetNode) == null) {
					mQueue.add(targetNode);
					newlabel++;
				}
				
				if (thisInpDetANode.getOutgoingNodes().contains(targetNode)) {
					Term newLabel = SmtUtils.or(mScript, thisInpDetANode.getOutgoingEdgeLabel(targetNode), edgelabel);
					thisInpDetANode.disconnectOutgoing(targetNode);
					thisInpDetANode.connectOutgoing(targetNode, newLabel);
				} else {
					thisInpDetANode.connectOutgoing(targetNode, edgelabel);
				}
			}
		}
		return initialPowerNode;
	}
}
