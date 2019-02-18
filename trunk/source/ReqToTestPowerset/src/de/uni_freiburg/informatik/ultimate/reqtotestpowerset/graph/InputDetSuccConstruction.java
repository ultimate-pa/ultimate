package de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqSymbolTable;

public class InputDetSuccConstruction {
	private final Script mScript;
	private final ManagedScript mManagedScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final GuardGraph mGuardGraph;
	private Set<GuardGraph> mSeenNodes;
	private LinkedList<GuardGraph> mQueue;
	private final Set<Term> mMonomials;
	private final Set<Term> mOutputVars;
	private final Sort mSort;
	private Set<GuardGraph> mAutStates;
	private Term mTrue;
	private Term mFalse;
	private SearchGraphTable mSGTable;
	
	public InputDetSuccConstruction(ManagedScript managedScript, IUltimateServiceProvider services,
			ILogger logger, GuardGraph powersetAuto, Script script, ReqSymbolTable symboltable) {
		mManagedScript = managedScript;
		mServices = services;
		mLogger = logger;
		mScript = script;
		mSeenNodes = new HashSet<GuardGraph>();
		mQueue = new LinkedList<GuardGraph>();
		mAutStates = new HashSet<>();
		mSort = mScript.sort("Bool");
		mMonomials = createMonomials(symboltable);
		mOutputVars = getOutputVariables(symboltable.getOutputVars());
		makeTrueAndFalse();
		mGuardGraph = constructInputDetSuccAutomaton(powersetAuto);
		mSGTable = new SearchGraphTable(logger, script);
		populateSearchGraph();
		mLogger.warn(mSGTable);
		mSGTable.makeTests();
		mLogger.warn(mSGTable.getNrOfFinals());
		mLogger.warn(mSGTable.getNrOfTests());
	}

	private void makeTrueAndFalse() {
		for (Term t : mMonomials) {
			Term nt = SmtUtils.not(mScript, t);
			mFalse = SmtUtils.and(mScript, t, nt);
			mTrue = SmtUtils.or(mScript, t, nt);
			break;
		}
	}
	
	private Set<Term> getOutputVariables(Set<String> inputVars) {
		Set<Term> result = new HashSet<>();
		for (String varname : inputVars) {
			Term a = mScript.variable(varname, mSort);
			Term na = SmtUtils.not(mScript, a);
			result.add(a);
			result.add(na);
		}
		return result;
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
				Set<GuardGraph> succsrs = getAllSuccessors(thisInpDetANode.getBuildingNodes(), mon);

				GuardGraph targetNode = new GuardGraph(newlabel, succsrs);
				//TODO: refactor! take HashMap<set<GuardGraph>, GuardGraph> which stores the internal nodes i.e. succsrs and indexes nodes 
				// accordingly.
				if(collectionContains(mAutStates, targetNode) == null) {
					mAutStates.add(targetNode);
				} else {
					targetNode = collectionContains(mAutStates, targetNode);
				}
				
				Term edgelabel = getNewEdgeLabel(thisInpDetANode.getBuildingNodes(), succsrs, mon);
				
				if(collectionContains(mQueue, targetNode) == null && collectionContains(mSeenNodes, targetNode) == null) {
					mQueue.add(targetNode);
					newlabel++;
				}
				
				if (thisInpDetANode.getOutgoingNodes().contains(targetNode)) {
					Term newLabel = SmtUtils.or(mScript, thisInpDetANode.getOutgoingEdgeLabel(targetNode), edgelabel);
					thisInpDetANode.disconnectOutgoing(targetNode);
					thisInpDetANode.connectOutgoing(targetNode, newLabel);
					initialPowerNode.incEdges();
					
				} else {
					thisInpDetANode.connectOutgoing(targetNode, edgelabel);
					initialPowerNode.incEdges();
				}
				
			}
		}
		return initialPowerNode;
	}
	
	private Set<GuardGraph> getAllSuccessors(Set<GuardGraph> buildingNodes, Term monomial) {
		Set<GuardGraph> result = new HashSet<>();
		for (GuardGraph buildingNode : buildingNodes) {
			result.addAll(findSuccessors(buildingNode, monomial));
		}
		return result;
	}
	
	private Term getNewEdgeLabel(Set<GuardGraph> buildingNodes, Set<GuardGraph> successors, Term monomial) {
		// hack to create a false term for the later disjunction
		LinkedList<Term> termsOfDisjunction = new LinkedList<>();
		for (GuardGraph fromNode : buildingNodes) {
			for (GuardGraph toNode : successors) {
				if(fromNode.getSuccessors().contains(toNode)) {
					Term oldLabelToSuccessor =  fromNode.getOutgoingEdgeLabel(toNode);
					Term newLabelToSuccessor = SmtUtils.and(mScript, oldLabelToSuccessor, monomial);
					termsOfDisjunction.add(newLabelToSuccessor);
				}
			}
		}
		return makeDisj(outputTester(termsOfDisjunction));
	}
	
	/***
	 * Method test if any one output variable is present in each disjunction term
	 * Method removes output variables from disjunction terms if said output variable is not present in all the disjunction terms
	 * 
	 * @param disjTermToBeTested
	 * Term may or may not contain Output variables
	 * @return testedTerm
	 * Term contains the same output variable in all its disjuncs or none at all 
	 */
	private LinkedList<Term> outputTester(LinkedList<Term> termsToTest) {
		LinkedList<Term> localList = new LinkedList<>(termsToTest);
		Set<Term> oVarHelper = findOutputVars(termsToTest);
		
		if ( oVarHelper.size() == 0 ) {
			return termsToTest;
		} else {
			for ( Term ov : oVarHelper ) {
				if ( testTermsContainOVar(localList, ov) ) {
					continue;
				} else {
					localList = removeOVar(localList, ov);
				}
			}
			return localList;
		}
	}

	private LinkedList<Term> removeOVar(LinkedList<Term> localList, Term ov) {
		LinkedList<Term> helperList = new LinkedList<>();
		for ( Term t : localList ) {
			helperList.add(remakeTerm(t, ov));
		}
		return helperList;
	}

	private boolean testTermsContainOVar(List<Term> disjTerms, Term ov) {
		for (Term disjTerm : disjTerms) {
			boolean disjTermFlag = false;
			for (Term element : SmtUtils.getConjuncts(disjTerm)) {
				if (element.equals(ov)) {
					disjTermFlag = true;
				}
			}
			if (!disjTermFlag) {
				return false;
			}
		}
		return true;
	}

	// TODO this will not work if termToRemake is not a conjunction, I think
	// or a conjunction of conjunctions...
	private Term remakeTerm(Term termToRemake, Term oVar) {
		Term result = mTrue;
		Term dnf = SmtUtils.toDnf(mServices, mManagedScript, termToRemake,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		for (Term disjTerm : SmtUtils.getDisjuncts(dnf)) {
			for (Term element : SmtUtils.getConjuncts(disjTerm)) {
				if (!element.equals(oVar)) {
					result = SmtUtils.and(mScript, result, element);
				}
			}
		}
		return result;
	}

	private Set<Term> findOutputVars(LinkedList<Term> termsToTest) {
		Set<Term> result = new HashSet<>();
		for (Term element : termsToTest) {
			// find terms which are output variables
			for (Term x : element.getFreeVars()) {
				for (Term o : mOutputVars) {
					if(x.equals(o)) {
						result.add(x);
					}
				}
			}
		}
		return result;
	}

	private Term makeDisj(LinkedList<Term> terms) {
		Term result = mFalse;
		for ( Term t : terms ) {
			result = SmtUtils.or(mScript, result, t);
		}
		return result;
	}
	
	public void populateSearchGraph() {
		LinkedList<GuardGraph> open = new LinkedList<>();
		Set<GuardGraph> seen = new HashSet<>();
		
		
		mSGTable.add(mGuardGraph, 0, null, false);
		open.add(mGuardGraph);
		
		while (open.size() > 0) {
			GuardGraph workingNode = open.pop();
			seen.add(workingNode);
			
			for ( GuardGraph successor : workingNode.getOutgoingNodes()) {
				mSGTable.add(successor, mSGTable.getDistOfElement(workingNode) + 1, workingNode, isEndNode(successor));
				if ( !seen.contains(successor) && !open.contains(successor) ) {
					open.add(successor);
				}
			}
		}
	}
	
	private boolean isEndNode(GuardGraph node) {
		boolean localFlag = false;
		for ( Term oVar : mOutputVars ) {
			for ( GuardGraph succ : node.getOutgoingNodes() ) {
				Term[] disjs = SmtUtils.getDisjuncts(
						SmtUtils.toDnf(
								mServices, mManagedScript, node.getOutgoingEdgeLabel(succ),
								XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION));
				
				localFlag = localFlag || testTermsContainOVar(Arrays.asList(disjs), oVar);
			}
		}
		return localFlag;
	}
}
