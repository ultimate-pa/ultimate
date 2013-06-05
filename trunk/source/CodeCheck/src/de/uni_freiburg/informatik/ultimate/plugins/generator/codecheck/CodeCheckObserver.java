package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.Edge;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.structure.IWalkable;
//import de.uni_freiburg.informatik.ultimate.plugins.generator.impulse.AnnotatedProgrmPoint;
//import de.uni_freiburg.informatik.ultimate.plugins.generator.impulse.EmptinessCheck;
//import de.uni_freiburg.informatik.ultimate.plugins.generator.impulse.Pair;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
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
public class CodeCheckObserver implements IUnmanagedObserver {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.s_PLUGIN_ID);

	private RootNode m_originalRoot;
	private SmtManager m_smtManager;
	private TAPreferences m_taPrefs;
	private ImpRootNode m_graphRoot;

	private IPredicate m_truePredicate;
	private IPredicate m_falsePredicate;

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
	
	@Override
	public boolean process(IElement root) {
		
		
		final boolean loop_forever = true; // for DEBUG
		final int iterationsLimit = 100; // for DEBUG
		
		initialize(root);
		
		ImpRootNode originalGraphCopy = copyGraph(m_graphRoot);
		
		int noOfProcedures = originalGraphCopy.getOutgoingNodes().size();
		
		for (int procID = 0; procID < noOfProcedures; ++procID) {
			AnnotatedProgramPoint procRoot = m_graphRoot.getOutgoingNodes().get(procID);
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
						splitGraph(trace, interpolants, procedureRoot);
						System.out.println();
						
					} else {
						System.out.println("This program is UNSAFE.");
						break;
						// trace is feasible
						// return unsafe
					}
				}
			}
			m_graphRoot = copyGraph(originalGraphCopy);
		}
		
		return false;
	}
	
	private boolean splitGraph(AnnotatedProgramPoint[] nodes, IPredicate[] interpolants, AnnotatedProgramPoint procedureRoot) {
		HashMap <AnnotatedProgramPoint, ArrayList <AnnotatedProgramPoint>> nodesClones = new HashMap <AnnotatedProgramPoint, ArrayList <AnnotatedProgramPoint>>();

		HashMap <AnnotatedProgramPoint, ArrayList <IPredicate>> map = new HashMap <AnnotatedProgramPoint, ArrayList <IPredicate>>();
		
		for (int i = 1; i < nodes.length; ++i) {
			if (!map.containsKey(nodes[i])) {
				map.put(nodes[i], new ArrayList <IPredicate>());
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
	
	
	private boolean splitNode(AnnotatedProgramPoint oldNode, IPredicate[] interpolant, HashMap <AnnotatedProgramPoint, ArrayList <AnnotatedProgramPoint>> nodesClones) {
		
		int interpolantsCount = interpolant.length;
		AnnotatedProgramPoint[][] newNodes = new AnnotatedProgramPoint[interpolantsCount][2];
		for (int i = 0; i < interpolantsCount; ++i) {
			newNodes[i][0] = new AnnotatedProgramPoint(oldNode, conjugatePredicates(oldNode.getPredicate(), interpolant[i]));	
			newNodes[i][1] = new AnnotatedProgramPoint(oldNode, conjugatePredicates(oldNode.getPredicate(), negatePredicate(interpolant[i])));
		}
		List<AnnotatedProgramPoint> predecessorNodes = oldNode.getIncomingNodes();
		List<AnnotatedProgramPoint> successorNodes = oldNode.getOutgoingNodes();

        // {{{
		for (AnnotatedProgramPoint predecessorNode : predecessorNodes) {
			if (predecessorNode != oldNode) {
				CodeBlock label = predecessorNode.getOutgoingEdgeLabel(oldNode);
				System.out.println("Adding Edge: " + label);
				for (int i = 0; i < interpolantsCount; ++i) {
					for (AnnotatedProgramPoint newNode : newNodes[i]) {
						if (isValidEdge(predecessorNode, label, newNode)) {
							predecessorNode.addOutgoingNode(newNode, label);
							newNode.addIncomingNode(predecessorNode);
						}
					}
				}
				System.out.println("Added Edge: " + label);
				predecessorNode.removeOutgoingNode(oldNode);
			}
		}
        // }}}
		
        // {{{
		for (AnnotatedProgramPoint successorNode : successorNodes) {
			if (successorNode != oldNode) {
				CodeBlock label = oldNode.getOutgoingEdgeLabel(successorNode);
				boolean isReturn = label instanceof Return;
				System.out.println("Adding Edge: " + label);
				for (int i = 0; i < interpolantsCount; ++i) {
					for (AnnotatedProgramPoint newNode : newNodes[i]) {
						if (isValidEdge(newNode, label, successorNode)) {
							newNode.addOutgoingNode(successorNode, label);
							successorNode.addIncomingNode(newNode);
							if (isReturn) {
								HashSet <AnnotatedProgramPoint> hyper = successorNode.getCallPredsOfOutgoingReturnTarget(oldNode);
								for (Iterator <AnnotatedProgramPoint> it = hyper.iterator(); it.hasNext(); ) {
									AnnotatedProgramPoint src = it.next();
									if (nodesClones.containsKey(src)) {
										for (Iterator <AnnotatedProgramPoint> clone = nodesClones.get(src).iterator(); clone.hasNext(); ) {
											successorNode.addOutGoingReturnCallPred(oldNode, clone.next());
										}
										successorNode.removeIncomingNode(src);
									}
								}
							}
						}
					}
				}
				System.out.println("Added Edge: " + label);
				successorNode.removeIncomingNode(oldNode);
			}
		}
        // }}}
		
		boolean selfLoop = oldNode.getSuccessors().contains(oldNode);
		
        // {{{
		if (selfLoop) {
			CodeBlock label = oldNode.getOutgoingEdgeLabel(oldNode);
			for (int i = 0; i < interpolantsCount; ++i) {
				for (int j = 0; j < interpolantsCount; ++j) {
					// FIXME: Check if complete association required.
					for (AnnotatedProgramPoint source : newNodes[i]) {
						for (AnnotatedProgramPoint destination : newNodes[j]) {
							if (isValidEdge(source, label, destination)) {
								source.addOutgoingNode(destination, label);
								destination.addIncomingNode(source);
							}
						}
					}
				}
			}
		}
        // }}}
		System.out.println("Splitted node : " + oldNode.toString());
		
		nodesClones.put(oldNode, new ArrayList <AnnotatedProgramPoint>());
		for (int i = 0; i < interpolantsCount; ++i)
			for (AnnotatedProgramPoint node : newNodes[i])
				if (node != null)
					nodesClones.get(oldNode).add(node);
					
		return true;
	}
	
	private boolean splitNode(AnnotatedProgramPoint oldNode, IPredicate interpolant, HashMap <AnnotatedProgramPoint, ArrayList <AnnotatedProgramPoint>> nodesClones) {
		return splitNode(oldNode, new IPredicate[]{interpolant}, nodesClones);
	}
	
	private boolean isValidEdge(AnnotatedProgramPoint sourceNode, CodeBlock edgeLabel,
			AnnotatedProgramPoint destinationNode) {
		if (edgeLabel instanceof DummyCodeBlock)
			return false;
		System.out.print(".");
		return m_smtManager.isInductive(sourceNode.getPredicate(), edgeLabel, negatePredicate(destinationNode.getPredicate())) != LBool.UNSAT;
	}
    // {{{

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
    // }}}
}
