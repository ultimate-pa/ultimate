package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Stack;


import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceValues.Solver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;

import org.apache.log4j.Logger;
//import org.eclipse.swt.program.Program;


/**
 * Auto-Generated Stub for the plug-in's Observer
 */

enum Checker {
	ULTIMATE, IMPULSE
}

public class CodeCheckObserver implements IUnmanagedObserver {

	private Checker checker;
	public static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	private CodeChecker codeChecker;
	
	public RootNode m_originalRoot;
	public TAPreferences m_taPrefs;
	
	public SmtManager m_smtManager;
	public IPredicate m_truePredicate;
	public IPredicate m_falsePredicate;
	
	public ImpRootNode m_graphRoot;

	
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

	public ImpRootNode copyGraph(ImpRootNode root) {
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
			for (AnnotatedProgramPoint nextNode : nextNodes) {
				if (!copy.containsKey(nextNode)) {
					stack.add(nextNode);
				}
			}
		}
		for (AnnotatedProgramPoint node : copy.keySet()) {
			AnnotatedProgramPoint newNode = copy.get(node);
			List <AnnotatedProgramPoint> nextNodes = node.getOutgoingNodes();
			for (AnnotatedProgramPoint nextNode : nextNodes) {
				AnnotatedProgramPoint nextNewNode = copy.get(nextNode);
				newNode.addOutgoingNode(nextNewNode, node.getOutgoingEdgeLabel(nextNode));
				nextNewNode.addIncomingNode(newNode);
			}
			AnnotatedProgramPoint[] returnNodes = node.m_outgoingReturnAppToCallPreds.keySet().toArray(new AnnotatedProgramPoint[]{});
			for (AnnotatedProgramPoint returnNode : returnNodes) {
				AnnotatedProgramPoint[] callNodes = node.m_outgoingReturnAppToCallPreds.get(returnNode).toArray(new AnnotatedProgramPoint[]{});
				for (AnnotatedProgramPoint callNode : callNodes) {
					node.m_outgoingReturnAppToCallPreds.get(returnNode).add(copy.get(callNode));
					node.m_outgoingReturnAppToCallPreds.get(returnNode).remove(callNode);
				}
				node.m_outgoingReturnAppToCallPreds.put(copy.get(returnNode), node.m_outgoingReturnAppToCallPreds.get(returnNode));
				node.m_outgoingReturnAppToCallPreds.remove(returnNode);
			}
			AnnotatedProgramPoint[] hyperNodes = node.m_ingoingReturnAppToCallPreds.keySet().toArray(new AnnotatedProgramPoint[]{});
			for (AnnotatedProgramPoint hyperNode : hyperNodes) {
				AnnotatedProgramPoint[] preRets = node.m_ingoingReturnAppToCallPreds.get(hyperNode).toArray(new AnnotatedProgramPoint[]{});
				for (AnnotatedProgramPoint preRet : preRets) {
					node.m_ingoingReturnAppToCallPreds.get(hyperNode).add(copy.get(preRet));
					node.m_ingoingReturnAppToCallPreds.get(hyperNode).remove(preRet);
				}
				node.m_ingoingReturnAppToCallPreds.put(copy.get(hyperNode), node.m_ingoingReturnAppToCallPreds.get(hyperNode));
				node.m_ingoingReturnAppToCallPreds.remove(hyperNode);
			}
		}
		return newRoot;
	}
	
	public boolean initialize(IElement root) {
		m_originalRoot = (RootNode) root;
		RootAnnot rootAnnot = m_originalRoot.getRootAnnot();
		m_taPrefs = rootAnnot.getTaPrefs();
		m_smtManager = new SmtManager(rootAnnot.getBoogie2Smt(),
				Solver.SMTInterpol, rootAnnot.getGlobalVars(),
				rootAnnot.getModGlobVarManager(), false, "");

		m_truePredicate = m_smtManager.newTruePredicate();
		m_falsePredicate = m_smtManager.newFalsePredicate();
		RCFG2AnnotatedRCFG r2ar = new RCFG2AnnotatedRCFG(m_smtManager);
		m_graphRoot = r2ar.convert(m_originalRoot, m_truePredicate);

		if (checker == Checker.IMPULSE) {
			codeChecker = new ImpulseChecker(root, m_smtManager, m_truePredicate, m_falsePredicate, m_taPrefs, m_originalRoot, m_graphRoot);
		} else {
			codeChecker = new UltimateChecker(root, m_smtManager, m_truePredicate, m_falsePredicate, m_taPrefs, m_originalRoot, m_graphRoot);
		}
		return false;
	}
	
	public boolean process(IElement root) {
		//FIXME
		checker = Checker.ULTIMATE;
		
		initialize(root);
		
		final boolean loop_forever = true; // for DEBUG
		final int iterationsLimit = 0; // for DEBUG
		
		//ImpRootNode originalGraphCopy = copyGraph(m_graphRoot);
		
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
				s_Logger.debug(String.format("Iterations = %d\n", iterationsCount));
				codeChecker.debug();
				if (stack.isEmpty()) {
					s_Logger.info("This Program is SAFE, Check terminated with " + iterationsCount + " iterations.");
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
					s_Logger.info("Error Path is FOUND.");
					TraceChecker traceChecker = new TraceChecker(m_smtManager, 
							m_originalRoot.getRootAnnot().getModGlobVarManager(), 
							m_originalRoot.getRootAnnot().getEntryNodes(),
							dumpInitialize());
					LBool isSafe = traceChecker.checkTrace(m_truePredicate, // checks whether the trace is feasible, i.e. the formula is satisfiable
														   m_falsePredicate,  //return LBool.UNSAT if trace is infeasible
														   errorNWP.getSecond());
					
					if(isSafe == LBool.UNSAT) { //trace is infeasible
						IPredicate[] interpolants = traceChecker.getInterpolants(new TraceChecker.AllIntegers());
						
						AnnotatedProgramPoint[] trace = errorNWP.getFirst();
						codeChecker.codeCheck(trace, interpolants, procedureRoot);
						
						System.out.println();
						
					} else { // trace is feasible
						s_Logger.info("This program is UNSAFE, Check terminated with " + iterationsCount + " iterations.");
						return false; //break
					}
				}
			}
			codeChecker.debug();
			//if (procID < noOfProcedures)
			//m_graphRoot = copyGraph(originalGraphCopy);
		}
		
		return false;
	}
	// Debug
	
	public ImpRootNode getRoot() {
		return codeChecker.m_graphRoot;
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