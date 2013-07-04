package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Stack;

import javax.annotation.PreDestroy;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceValues.Solver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;

import org.apache.log4j.Logger;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
enum Checker {
	ULTIMATE, IMPULSE
}

enum RedirectionMethod {
	First, FirstStrongest, Random, RandomStrongest, Alex
}

public class CodeCheckObserver implements IUnmanagedObserver {

	private static Checker checker;
	private static RedirectionMethod redirectionMethod;
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.s_PLUGIN_ID);

	private RootNode m_originalRoot;
	private SmtManager m_smtManager;
	private TAPreferences m_taPrefs;
	private ImpRootNode m_graphRoot;

	private IPredicate m_truePredicate;
	private IPredicate m_falsePredicate;
	
	private HashMap <AnnotatedProgramPoint, HashMap<IPredicate, AnnotatedProgramPoint>> LocationPredicates;

	
	
	public boolean initialize(IElement root) {
		m_originalRoot = (RootNode) root;
		RootAnnot rootAnnot = m_originalRoot.getRootAnnot();
		m_taPrefs = rootAnnot.getTaPrefs();
		m_smtManager = new SmtManager(rootAnnot.getBoogie2Smt(),
				Solver.SMTInterpol, rootAnnot.getGlobalVars(),
				rootAnnot.getModifiedVars(), false, "");

		m_truePredicate = m_smtManager.newTruePredicate();
		m_falsePredicate = m_smtManager.newFalsePredicate();

		RCFG2AnnotatedRCFG r2ar = new RCFG2AnnotatedRCFG(m_smtManager);
		m_graphRoot = r2ar.convert(m_originalRoot, m_truePredicate);

		return true;
	}
	
	

	private PrintWriter dumpInitialize() { // copied from Impulse, needed for trace checker
		File file = 
				new File(m_taPrefs.dumpPath() + "/" + ".txt");
		FileWriter fileWriter;
		try {
			fileWriter = new FileWriter(file);
			return new PrintWriter(fileWriter);
		} catch (IOException e) {
			e.printStackTrace();
		} 
		return null;
	}

	private IPredicate conjugatePredicates(IPredicate a, IPredicate b) {
		TermVarsProc tvp = m_smtManager.and(a, b);
		return m_smtManager.newPredicate(tvp.getFormula(), tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
	}
	
	private IPredicate negatePredicate(IPredicate a) {
		TermVarsProc tvp = m_smtManager.not(a);
		return m_smtManager.newPredicate(tvp.getFormula(), tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
	}
	
	private ImpRootNode copyGraph(ImpRootNode root) {
		HashMap <AnnotatedProgramPoint, AnnotatedProgramPoint> copy = new HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint>();
		
		ImpRootNode newRoot = new ImpRootNode(root.getRootAnnot());
		copy.put(root, newRoot);
		Stack <AnnotatedProgramPoint> stack = new Stack<AnnotatedProgramPoint>();
		for (AnnotatedProgramPoint child : root.getOutgoingNodes()) {
			stack.add(child);
		}
		while (!stack.isEmpty()) {
			AnnotatedProgramPoint current = stack.pop();
			if (copy.containsKey(current))
				continue;
			copy.put(current, new AnnotatedProgramPoint(current));
			List <AnnotatedProgramPoint> nextNodes = current.getOutgoingNodes();
			for (Iterator <AnnotatedProgramPoint> iterator = nextNodes.iterator(); iterator.hasNext(); ) {
				AnnotatedProgramPoint nextNode = iterator.next();
				if (!copy.containsKey(nextNode)) {
					stack.add(nextNode);
				}
			}
		}
		for (Iterator <AnnotatedProgramPoint> nodes = copy.keySet().iterator(); nodes.hasNext(); ) {
			AnnotatedProgramPoint node = nodes.next(), newNode = copy.get(node);
			List <AnnotatedProgramPoint> nextNodes = node.getOutgoingNodes();
			for (AnnotatedProgramPoint nextNode : nextNodes) {
				AnnotatedProgramPoint nextNewNode = copy.get(nextNode);
				newNode.addOutgoingNode(nextNewNode, node.getOutgoingEdgeLabel(nextNode));
				nextNewNode.addIncomingNode(newNode);
			}
		}
		return newRoot;
	}
	
	private boolean initializeLocationPredicates(AnnotatedProgramPoint node) {
		if(LocationPredicates.get(node) == null) {
			LocationPredicates.put(node, new HashMap<IPredicate,AnnotatedProgramPoint>());
			LocationPredicates.get(node).put(node.getPredicate(), node);
			for (AnnotatedProgramPoint successor : node.getOutgoingNodes())
				initializeLocationPredicates(successor);
		}
		return true;
	}
	
	@Override
	public boolean process(IElement root) {
		
		//FIXME
		checker = Checker.IMPULSE;
		redirectionMethod = RedirectionMethod.RandomStrongest; // Alex : Change that variable here
		
		
		final boolean loop_forever = true; // for DEBUG
		final int iterationsLimit = 5; // for DEBUG
		
		initialize(root);
		
		ImpRootNode originalGraphCopy = copyGraph(m_graphRoot);
		
		if(checker == Checker.IMPULSE) {
			LocationPredicates= new HashMap<AnnotatedProgramPoint, HashMap<IPredicate,AnnotatedProgramPoint>>();
			initializeLocationPredicates(originalGraphCopy);
		}
		
		 /* testing copy graph
		
		m_graphRoot.addOutgoingNode(originalGraphCopy, new DummyCodeBlock());
		originalGraphCopy.addIncomingNode(m_graphRoot);
		
		if(true)
			return false;
		
		// */
		int noOfProcedures = m_graphRoot.getOutgoingNodes().size();
		
		for (int procID = 0; procID < 1 && procID < noOfProcedures; ++procID) {
			AnnotatedProgramPoint procRoot = m_graphRoot.getOutgoingNodes().get(procID);
			System.err.println("Exploring : " + procRoot);
			Stack <AnnotatedProgramPoint> stack = new Stack <AnnotatedProgramPoint>();
			stack.add(procRoot);
			EmptinessCheck emptinessCheck = new EmptinessCheck();
			int iterationsCount = 0; // for DEBUG
			while (loop_forever | iterationsCount++ < iterationsLimit) {
				System.out.printf("Iterations = %d\n", iterationsCount);
				if (stack.isEmpty()) {
					System.out.println("This Program is SAFE.");
					break;
				}
				AnnotatedProgramPoint procedureRoot = stack.peek();
				Pair<AnnotatedProgramPoint[], NestedWord<CodeBlock>> errorNWP = 
						emptinessCheck.checkForEmptiness(procedureRoot);
				
				if (errorNWP == null) {
					// if an error trace doesn't exist, return safe
					stack.pop();
					continue;
				} else {
					System.out.println("Error Path is FOUND.");
					TraceChecker traceChecker = new TraceChecker(m_smtManager, 
							m_originalRoot.getRootAnnot().getModifiedVars(), 
							m_originalRoot.getRootAnnot().getEntryNodes(),
							dumpInitialize());
					LBool isSafe = traceChecker.checkTrace(m_truePredicate, // checks whether the trace is feasible, i.e. the formula is satisfiable
														   m_falsePredicate,  //return LBool.UNSAT if trace is infeasible
														   errorNWP.getSecond());
					
					if(isSafe == LBool.UNSAT) { //trace is infeasible
						
						IPredicate[] interpolants = traceChecker.getInterpolants(new TraceChecker.AllIntegers());
						
						AnnotatedProgramPoint[] trace = errorNWP.getFirst();
						/*
						for (int i = 0; i < interpolants.length; i++)
							splitNode(trace[i + 1], interpolants[i]);
						*/
						switch(checker) {
						case ULTIMATE:
							ultimateCheck(trace, interpolants, procedureRoot);
							break;
						case IMPULSE:
							impulseCheck(trace, interpolants, procedureRoot);
							break;
						}
						
						System.out.println();
						
					} else {
						System.out.println("This program is UNSAFE.");
						return false;
						//break;
						// trace is feasible
						// return unsafe
					}
				}
			}
			//if (procID < noOfProcedures)
			//m_graphRoot = copyGraph(originalGraphCopy);
		}
		
		return false;
	}
	
	private boolean ultimateCheck(AnnotatedProgramPoint[] nodes, IPredicate[] interpolants, AnnotatedProgramPoint procedureRoot) {
		
		ArrayList <AnnotatedProgramPoint> hallo = new ArrayList<AnnotatedProgramPoint>();
		for (AnnotatedProgramPoint x : nodes) hallo.add(x);
		System.err.println("Error: " + hallo);
		
		ArrayList <IPredicate> hello = new ArrayList<IPredicate>();
		for (IPredicate x : interpolants) hello.add(x);
		System.err.println("Inter: " + hello);
		System.err.println();
		
		
		HashMap <AnnotatedProgramPoint, ArrayList <AnnotatedProgramPoint>> nodesClones = new HashMap <AnnotatedProgramPoint, ArrayList <AnnotatedProgramPoint>>();
		// nodesClones.clear();
		
		HashMap <AnnotatedProgramPoint, ArrayList <IPredicate>> map = new HashMap <AnnotatedProgramPoint, ArrayList <IPredicate>>();
		
		for (int i = 0; i < interpolants.length; ++i) {
			if (!map.containsKey(nodes[i + 1])) {
				map.put(nodes[i + 1], new ArrayList <IPredicate>());
			}
		}
		for (int i = 0; i < interpolants.length; ++i) {
			map.get(nodes[i + 1]).add(interpolants[i]);
		}
		for (Iterator <AnnotatedProgramPoint> it = map.keySet().iterator(); it.hasNext(); ) {
			AnnotatedProgramPoint node = it.next();
			if (node == procedureRoot) {
				map.get(node).add(m_truePredicate);
			}

			splitNode(node, map.get(node).toArray(new IPredicate[]{}), nodesClones);
			
		}
		return true;
	}
		
	private boolean modifyHyperEdges(AnnotatedProgramPoint src, AnnotatedProgramPoint dest, HashMap <AnnotatedProgramPoint, ArrayList <AnnotatedProgramPoint>> nodesClones) {
		HashSet <AnnotatedProgramPoint> hyperEdges = src.getCallPredsOfOutgoingReturnTarget(dest);
		if (hyperEdges != null) {
			for (Iterator <AnnotatedProgramPoint> it = hyperEdges.iterator(); it.hasNext(); ) {
				AnnotatedProgramPoint callPoint = it.next();
				if (nodesClones.containsKey(callPoint)) {
					for (Iterator <AnnotatedProgramPoint> clone = nodesClones.get(callPoint).iterator(); clone.hasNext(); ) {
						src.addOutGoingReturnCallPred(dest, clone.next());
					}
					src.removeOutgoingReturnCallPred(dest, callPoint);
				}
			}
		}
		return true;
	}
	
	private boolean splitNode(AnnotatedProgramPoint oldNode, IPredicate[] interpolant, HashMap <AnnotatedProgramPoint, ArrayList <AnnotatedProgramPoint>> nodesClones) {
		
		int interpolantsCount = interpolant.length;
		AnnotatedProgramPoint[][] newNodes = new AnnotatedProgramPoint[interpolantsCount][2];
		for (int i = 0; i < interpolantsCount; ++i) {
			newNodes[i] = new AnnotatedProgramPoint[] {
					new AnnotatedProgramPoint(oldNode, conjugatePredicates(oldNode.getPredicate(), interpolant[i])),
					new AnnotatedProgramPoint(oldNode, conjugatePredicates(oldNode.getPredicate(), negatePredicate(interpolant[i])))
					};
		}
		
		AnnotatedProgramPoint[] predecessorNodes = oldNode.getIncomingNodes().toArray(new AnnotatedProgramPoint[]{});
		AnnotatedProgramPoint[] successorNodes = oldNode.getOutgoingNodes().toArray(new AnnotatedProgramPoint[]{});
		
		
		for (AnnotatedProgramPoint predecessorNode : predecessorNodes) {
			if (predecessorNode != oldNode) {
				CodeBlock label = predecessorNode.getOutgoingEdgeLabel(oldNode);
				HashSet <AnnotatedProgramPoint> hyperEdges = predecessorNode.getCallPredsOfOutgoingReturnTarget(oldNode);
				boolean isReturn = label instanceof Return;
				for (int i = 0; i < interpolantsCount; ++i) {
					for (AnnotatedProgramPoint newNode : newNodes[i]) {
						if (isSatEdge(predecessorNode, label, newNode)) {
							predecessorNode.addOutgoingNode(newNode, label);
							newNode.addIncomingNode(predecessorNode);
							if (isReturn) {
								/*
								modifyHyperEdges(predecessorNode, newNode, nodesClones);
								for (AnnotatedProgramPoint node : hyperEdges) {
									predecessorNode.addOutGoingReturnCallPred(newNode, node);
								}
								*/
							}
						}
					}
				}
				/*
				for (AnnotatedProgramPoint node : hyperEdges)
					predecessorNode.removeOutgoingReturnCallPred(oldNode, node);
				*/
				oldNode.removeIncomingNode(predecessorNode);
				predecessorNode.removeOutgoingNode(oldNode);
			}
		}

		for (AnnotatedProgramPoint successorNode : successorNodes) {
			if (successorNode != oldNode) {
				CodeBlock label = oldNode.getOutgoingEdgeLabel(successorNode);
				boolean isReturn = label instanceof Return;
				for (int i = 0; i < interpolantsCount; ++i) {
					for (AnnotatedProgramPoint newNode : newNodes[i]) {
						if (isSatEdge(newNode, label, successorNode)) {
							newNode.addOutgoingNode(successorNode, label);
							successorNode.addIncomingNode(newNode);
							if (isReturn) {
								//modifyHyperEdges(newNode, successorNode, nodesClones);
							}
						}
					}
				}
				successorNode.removeIncomingNode(oldNode);
				oldNode.removeOutgoingNode(successorNode);
			}
		}
		
		
		boolean selfLoop = oldNode.getSuccessors().contains(oldNode);
		
		if (selfLoop) {
			// FIXME: Check if complete association required.
			CodeBlock label = oldNode.getOutgoingEdgeLabel(oldNode);
			for (int i = 0; i < interpolantsCount; ++i) {
				for (AnnotatedProgramPoint source : newNodes[i]) {
					for (AnnotatedProgramPoint destination : newNodes[i]) {
						if (isSatEdge(source, label, destination)) {
							source.addOutgoingNode(destination, label);
							destination.addIncomingNode(source);
						}
					}
				}
			}
		}
		//System.out.println("Splitted node : " + oldNode.toString());
		
		nodesClones.put(oldNode, new ArrayList <AnnotatedProgramPoint>());
		for (int i = 0; i < interpolantsCount; ++i) {
			for (AnnotatedProgramPoint node : newNodes[i]) {
				if (node != null) {
					nodesClones.get(oldNode).add(node);
				}
			}
		}
				
		/*
		ArrayList<AnnotatedProgramPoint> preReturn = new ArrayList<AnnotatedProgramPoint>();
		for (Iterator <AnnotatedProgramPoint> it = oldNode.getReturnEdgesIterator(); it.hasNext(); preReturn.add(it.next()));

		for (Iterator <AnnotatedProgramPoint> preRetIt = preReturn.iterator(); preRetIt.hasNext(); ) {
			AnnotatedProgramPoint preRet = preRetIt.next(), target = oldNode.getReturnPoint(preRet);
			
			for (Iterator <AnnotatedProgramPoint> clones = nodesClones.get(oldNode).iterator(); clones.hasNext(); ) {
				AnnotatedProgramPoint nodeClone = clones.next();
				preRet.addOutGoingReturnCallPred(target, nodeClone);
			}
			
			preRet.removeOutgoingReturnCallPred(target, oldNode);
		}
		*/
		
		for (HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>> map : AnnotatedProgramPoint.m_ingoing) {
			if (map.containsKey(oldNode)) {
				HashSet <AnnotatedProgramPoint> hyperEdges = map.get(oldNode);
				for (Iterator <AnnotatedProgramPoint> clones = nodesClones.get(oldNode).iterator(); clones.hasNext(); ) {
					AnnotatedProgramPoint newNode = clones.next();
					map.put(newNode, hyperEdges);
				}
				map.remove(oldNode);
			}
		}
		
		for (HashSet<AnnotatedProgramPoint> set : AnnotatedProgramPoint.m_in) {
			if (set.contains(oldNode)) {
				for (Iterator <AnnotatedProgramPoint> clones = nodesClones.get(oldNode).iterator(); clones.hasNext(); ) {
					AnnotatedProgramPoint newNode = clones.next();
					set.add(newNode);
				}
				set.remove(oldNode);
			}
		}
		return true;
	}
	
	private boolean isSatEdge(AnnotatedProgramPoint sourceNode, CodeBlock edgeLabel,
			AnnotatedProgramPoint destinationNode) {
		//FIXME
		if (edgeLabel instanceof DummyCodeBlock)
			return false;
		System.out.print(".");
		return m_smtManager.isInductive(sourceNode.getPredicate(), edgeLabel, negatePredicate(destinationNode.getPredicate())) != LBool.UNSAT;
	}
	
	private boolean isValidEdge(AnnotatedProgramPoint sourceNode, CodeBlock edgeLabel,
			AnnotatedProgramPoint destinationNode) {
		//FIXME
		if (edgeLabel instanceof DummyCodeBlock)
			return false;
		System.out.print(".");
		return m_smtManager.isInductive(sourceNode.getPredicate(), edgeLabel, destinationNode.getPredicate()) == LBool.UNSAT;
	}

	private boolean impulseCheck (AnnotatedProgramPoint[] nodes, IPredicate[] interpolants, AnnotatedProgramPoint procedureRoot) {
		
		AnnotatedProgramPoint[] copies = new AnnotatedProgramPoint[interpolants.length + 1];
		for(int i = 1; i < copies.length; ++i) {
			copies[i] = copyNode(nodes[i], interpolants[i-1]);
		}
		
		redirectEdges(nodes, copies);
		
		for (AnnotatedProgramPoint node : nodes) {
			updateSets(node); 
			node.updateCopies();
		}
		
		return true;
		
	}

	private AnnotatedProgramPoint copyNode(AnnotatedProgramPoint oldNode, IPredicate interpolant) {
		
		
		/*   // Alex
		if(interpolant == m_truePredicate) // Alex :
			return oldNode;
		
		
		AnnotatedProgramPoint nodeRoot = oldNode.getCopyRoot();
		
		IPredicate newPredicate = conjugatePredicates(oldNode.getPredicate(), interpolant);

		if(LocationPredicates.get(nodeRoot).containsKey(newPredicate))
			return LocationPredicates.get(nodeRoot).get(newPredicate);
		*/
		
		IPredicate newPredicate = conjugatePredicates(oldNode.getPredicate(), interpolant);

		AnnotatedProgramPoint newNode = new AnnotatedProgramPoint(oldNode, newPredicate);
		
		//LocationPredicates.get(nodeRoot).put(newPredicate, newNode);
		
		oldNode.addCopy(newNode);
		newNode.setCloneSource(oldNode);

		AnnotatedProgramPoint[] successorNodes = oldNode.getOutgoingNodes().toArray(new AnnotatedProgramPoint[]{});
		
		for (AnnotatedProgramPoint successorNode : successorNodes) {
			
			CodeBlock label = oldNode.getOutgoingEdgeLabel(successorNode);
			newNode.addOutgoingNode(successorNode, label);
			successorNode.addIncomingNode(newNode);
			
		}
		
		return newNode;
	}
	
	private boolean redirectEdges(AnnotatedProgramPoint[] nodes, AnnotatedProgramPoint[] copies) {
		defaultRedirecting(nodes, copies);
		
		// Here you can use the tree instead, But I am now using the immediate copies
		
		for (AnnotatedProgramPoint node : nodes) {
			
			AnnotatedProgramPoint[] predecessorNodes = node.getIncomingNodes().toArray(new AnnotatedProgramPoint[]{});
			
			for (AnnotatedProgramPoint predecessorNode : predecessorNodes) {
				
				if(predecessorNode == m_graphRoot) //FIXME
					continue;
				
				AnnotatedProgramPoint bestRedirectTarget = findBestRedirectionTarget(predecessorNode, node);
				
				if(bestRedirectTarget == null)
					continue;
				
				CodeBlock label = predecessorNode.getOutgoingEdgeLabel(node);
				predecessorNode.removeOutgoingNode(node);
				node.removeIncomingNode(predecessorNode);

				predecessorNode.addOutgoingNode(bestRedirectTarget, label);
				bestRedirectTarget.addIncomingNode(predecessorNode);
			}
			
			
		}
		
		for (AnnotatedProgramPoint node : nodes) {
			node.updateCopies();
		}
		return true;
	}
		
	private boolean defaultRedirecting(AnnotatedProgramPoint[] nodes, AnnotatedProgramPoint[] copies) {
		
		for(int i = 0; i < copies.length; ++i) {

			AnnotatedProgramPoint source = copies[i];
			AnnotatedProgramPoint oldDest = nodes[i+1];
			
			
			if(i == 0)
				source = nodes[0];
			
			CodeBlock label = source.getOutgoingEdgeLabel(oldDest);
			source.removeOutgoingNode(oldDest);
			oldDest.removeIncomingNode(source);
			
			if(i < copies.length - 1) {
				AnnotatedProgramPoint newDest = copies[i + 1];
				source.addOutgoingNode(newDest, label);
				newDest.addIncomingNode(source);
			}
			
		}
		
		return true;
	}
	
	private boolean updateSets(AnnotatedProgramPoint copiedNode) {

		for (HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>> map : AnnotatedProgramPoint.m_ingoing) {
			if (map.containsKey(copiedNode)) {
				HashSet <AnnotatedProgramPoint> hyperEdges = map.get(copiedNode);
				for (Iterator <AnnotatedProgramPoint> clones = copiedNode.getNewCopies().iterator(); clones.hasNext(); ) {
					AnnotatedProgramPoint newNode = clones.next();
					map.put(newNode, hyperEdges);
				}
			}
		}
		
		for (HashSet<AnnotatedProgramPoint> set : AnnotatedProgramPoint.m_in) {
			if (set.contains(copiedNode)) {
				for (Iterator <AnnotatedProgramPoint> clones = copiedNode.getNewCopies().iterator(); clones.hasNext(); ) {
					AnnotatedProgramPoint newNode = clones.next();
					set.add(newNode);
				}
			}
		}
		
		return true;
		
	}
	
	private AnnotatedProgramPoint findBestRedirectionTarget(
			AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint node) {
		switch(redirectionMethod) {
		case First: return findFirstRedirectionTarget(predecessorNode, node);
		case FirstStrongest: return findFirstStrongestRedirectionTarget(predecessorNode, node);
		case Random: return findRandomRedirectionTarget(predecessorNode, node);
		case RandomStrongest: return findRandomStrongestRedirectionTarget(predecessorNode, node);
		case Alex: return null; //FIXME // Alex : Write your redirection algorithm here.
		default: return null;
		}
		//return result;
	}
	
	private AnnotatedProgramPoint findFirstRedirectionTarget(AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint node) {

		CodeBlock label = predecessorNode.getOutgoingEdgeLabel(node);
		
		ArrayList <AnnotatedProgramPoint> candidates = node.getNewCopies();
		
		for (AnnotatedProgramPoint candidate : candidates) {
			if(isValidEdge(predecessorNode, label, candidate)) {
				return candidate;
			}
		}
		
		return null;
		
	}
	
	private AnnotatedProgramPoint findFirstStrongestRedirectionTarget(AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint node) {

		CodeBlock label = predecessorNode.getOutgoingEdgeLabel(node);
		
		ArrayList <AnnotatedProgramPoint> candidates = node.getNewCopies();
		
		AnnotatedProgramPoint target = null;
		
		CodeBlock dummyLabel = new DummyCodeBlock();
		
		for (AnnotatedProgramPoint candidate : candidates) {
			if(isValidEdge(predecessorNode, label, candidate)) {
				if(target == null || isValidEdge(target, dummyLabel, candidate))
					target = candidate;
			}
		}
		
		return target;
		
	}
	
	private AnnotatedProgramPoint findRandomRedirectionTarget(AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint node) {

		CodeBlock label = predecessorNode.getOutgoingEdgeLabel(node);
		
		ArrayList <AnnotatedProgramPoint> candidates = node.getNewCopies();
		
		Collections.shuffle(candidates);
		
		for (AnnotatedProgramPoint candidate : candidates) {
			if(isValidEdge(predecessorNode, label, candidate)) {
				return candidate;
			}
		}
		
		return null;
		
	}
	
	private AnnotatedProgramPoint findRandomStrongestRedirectionTarget(AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint node) {

		CodeBlock label = predecessorNode.getOutgoingEdgeLabel(node);
		
		ArrayList <AnnotatedProgramPoint> candidates = node.getNewCopies();
		
		Collections.shuffle(candidates);
		
		AnnotatedProgramPoint target = null;
		
		CodeBlock dummyLabel = new DummyCodeBlock();
		
		for (AnnotatedProgramPoint candidate : candidates) {
			if(isValidEdge(predecessorNode, label, candidate)) {
				if(target == null || isValidEdge(target, dummyLabel, candidate))
					target = candidate;
			}
		}
		
		return target;
		
	}
		
	public ImpRootNode getRoot() {
		return m_graphRoot;
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
