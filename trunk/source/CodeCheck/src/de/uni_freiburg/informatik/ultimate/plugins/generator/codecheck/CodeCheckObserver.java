package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.structure.IWalkable;
//import de.uni_freiburg.informatik.ultimate.plugins.generator.impulse.AnnotatedProgrmPoint;
//import de.uni_freiburg.informatik.ultimate.plugins.generator.impulse.EmptinessCheck;
//import de.uni_freiburg.informatik.ultimate.plugins.generator.impulse.Pair;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
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

	public boolean BreadthFirstSearch() {

		LinkedList<AnnotatedProgramPoint> queue = new LinkedList<AnnotatedProgramPoint>();
		HashSet<AnnotatedProgramPoint> visited = new HashSet<AnnotatedProgramPoint>();
		
		boolean found = false;

		queue.add(m_graphRoot);
		while (!queue.isEmpty()) {
			AnnotatedProgramPoint top = queue.poll();
			System.out.printf("Node = %s; pred = %s\n", top, top.getPredicate());

			if (!visited.contains(top)) {
				visited.add(top);
				found |= top.isErrorLocation();
				if (found) {
					System.out.println("Found!!!");
					// return found;
				}
				List<IWalkable> adj = top.getSuccessors();
				for (Iterator<IWalkable> it = adj.iterator(); it.hasNext();) {
					AnnotatedProgramPoint nextNode = (AnnotatedProgramPoint) it
							.next();
					if (!visited.contains(nextNode)) {
						queue.add(nextNode);
					}
				}
			}
		}
		return found;
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
	
	@Override
	public boolean process(IElement root) {
		
		final boolean loop_forever = false; // for DEBUG
		final int iterationsLimit = 100; // for DEBUG
		
		initialize(root);
		
		for (AnnotatedProgramPoint procRoot : m_graphRoot.getOutgoingNodes()) {
			EmptinessCheck emptinessCheck = new EmptinessCheck();
			int iterationsCount = 0; // for DEBUG
			while (loop_forever || iterationsCount++ < iterationsLimit) {
				System.out.printf("Iterations = %d\n", iterationsCount);
				Pair<AnnotatedProgramPoint[], NestedWord<CodeBlock>> errorNWP = 
						emptinessCheck.checkForEmptiness(procRoot);
				
				if (errorNWP == null) {
					// if an error trace doesn't exist, return safe
					System.out.println("This Program is SAFE.");
					break;
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
						
						System.out.printf("Trace INFEASIBLE.\n Interpolants = %d, Trace = %d\n", interpolants.length, trace.length);
						for (int i = 0; i < interpolants.length; i++)
							splitNode(trace[i + 1], interpolants[i]);
						
					} else { 
						System.out.println("This program is UNSAFE.");
						break;
						// trace is feasible
						// return unsafe
					}
				}
			}
		}
		
		return false;
		
	}

	private boolean splitNode(AnnotatedProgramPoint oldNode, IPredicate interpolant) {
		AnnotatedProgramPoint[] newNodes = new AnnotatedProgramPoint[2];
		newNodes[0] = new AnnotatedProgramPoint(oldNode, conjugatePredicates(oldNode.getPredicate(), interpolant));	
		newNodes[1] = new AnnotatedProgramPoint(oldNode, conjugatePredicates(oldNode.getPredicate(), negatePredicate(interpolant)));
		
		List<AnnotatedProgramPoint> predecessorNodes = oldNode.getIncomingNodes();
		List<AnnotatedProgramPoint> successorNodes = oldNode.getOutgoingNodes();

		
		for (AnnotatedProgramPoint predecessorNode : predecessorNodes) {
			if (predecessorNode != oldNode) {
				CodeBlock label = predecessorNode.getOutgoingEdgeLabel(oldNode);
				for (AnnotatedProgramPoint newNode : newNodes) {
					if (isValidEdge(predecessorNode, label, newNode)) {
						predecessorNode.addOutgoingNode(newNode, label);
						newNode.addIncomingNode(predecessorNode);
					}
				}
				predecessorNode.removeOutgoingNode(oldNode);
			}
		}
		
		for (AnnotatedProgramPoint successorNode : successorNodes) {
			if (successorNode != oldNode) {
				CodeBlock label = oldNode.getOutgoingEdgeLabel(successorNode);
				for (AnnotatedProgramPoint newNode : newNodes) {
					if (isValidEdge(newNode, label, successorNode)) {
						newNode.addOutgoingNode(successorNode, label);
						successorNode.addIncomingNode(newNode);
					}
				}
				successorNode.removeIncomingNode(oldNode);
			}
		}
		
		boolean selfLoop = oldNode.getSuccessors().contains(oldNode);
		
		if (selfLoop) {
			CodeBlock label = oldNode.getOutgoingEdgeLabel(oldNode);
			for (AnnotatedProgramPoint source : newNodes) {
				for (AnnotatedProgramPoint destination : newNodes) {
					if (isValidEdge(source, label, destination)) {
						source.addOutgoingNode(destination, label);
						destination.addIncomingNode(source);
					}
				}
			}
		}
		
		//System.out.printf("\n\nOld Node:\n%s\nSplit into:\nNode #%d:\n%s\nNode #%d:\n%s\n\n\n", oldNode, 0, newNodes[0], 1, newNodes[1]);
		return true;
	}
	private boolean isValidEdge(AnnotatedProgramPoint sourceNode, CodeBlock edgeLabel,
			AnnotatedProgramPoint destinationNode) {
		return m_smtManager.isInductive(sourceNode.getPredicate(), edgeLabel, negatePredicate(destinationNode.getPredicate())) != LBool.UNSAT;
		//System.out.printf("\n\nSource Predicate = %s; Destination Predicate = %s; Edge = %s;\nEvaluates to %s\n\n\n", sourceNode.getPredicate(), destinationNode.getPredicate(), edgeLabel.getPrettyPrintedStatements(), r);
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
