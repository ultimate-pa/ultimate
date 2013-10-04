package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;


public abstract class CodeChecker {


	RootNode m_originalRoot;
	TAPreferences m_taPrefs;
	SmtManager m_smtManager;
	ImpRootNode m_graphRoot;

	IPredicate m_truePredicate;
	IPredicate m_falsePredicate;
	
	EdgeChecker m_edgeChecker;
	PredicateUnifier m_predicateUnifier;
	
	protected GraphWriter _graphWriter;
	
	public CodeChecker(IElement root, SmtManager smtManager, IPredicate truePredicate, IPredicate falsePredicate, 
			TAPreferences taPrefs, RootNode originalRoot, ImpRootNode graphRoot, GraphWriter graphWriter, EdgeChecker edgeChecker, PredicateUnifier predicateUnifier) {
		this.m_smtManager = smtManager;
		this.m_truePredicate = truePredicate;
		this.m_falsePredicate = falsePredicate;
		this.m_taPrefs = taPrefs;
		this.m_originalRoot = originalRoot;
		this.m_graphRoot = graphRoot;
		
		this.m_edgeChecker = edgeChecker;
		this.m_predicateUnifier = predicateUnifier;
		
		this._graphWriter = graphWriter;
	}
	
	public abstract boolean codeCheck(NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun, IPredicate[] interpolants, AnnotatedProgramPoint procedureRoot);

	/**
	 * Given 2 predicates, return a predicate which is the conjunction of both.
	 * @param a : The first Predicate.
	 * @param b : The second Predicate.
	 */
	protected IPredicate conjugatePredicates(IPredicate a, IPredicate b) {
		TermVarsProc tvp = m_smtManager.and(a, b);
		return m_predicateUnifier.getOrConstructPredicate(tvp.getFormula(), tvp.getVars(), tvp.getProcedures());
//		return m_smtManager.newPredicate(tvp.getFormula(), tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
	}
	
	/**
	 * Given a predicate, return a predicate which is the negation of it.
	 * @param a : The Predicate.
	 */
	protected IPredicate negatePredicate(IPredicate a) {
		TermVarsProc tvp = m_smtManager.not(a);
		return m_predicateUnifier.getOrConstructPredicate(tvp.getFormula(), tvp.getVars(), tvp.getProcedures());
//		return m_smtManager.newPredicate(tvp.getFormula(), tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
	}
	
	protected boolean isValidEdge(AnnotatedProgramPoint sourceNode, CodeBlock edgeLabel,
			AnnotatedProgramPoint destinationNode) {
		if (edgeLabel instanceof DummyCodeBlock)
			return false;
//		System.out.print(".");
		
		if (edgeLabel instanceof Call) 
			return m_smtManager.isInductiveCall(sourceNode.getPredicate(), (Call) edgeLabel, destinationNode.getPredicate()) == LBool.UNSAT;
		
		return m_smtManager.isInductive(sourceNode.getPredicate(), edgeLabel, destinationNode.getPredicate()) == LBool.UNSAT;
	}

	protected boolean isValidReturnEdge(AnnotatedProgramPoint sourceNode, CodeBlock edgeLabel,
			AnnotatedProgramPoint destinationNode, AnnotatedProgramPoint callNode) {
		return m_smtManager.isInductiveReturn(sourceNode.getPredicate(), callNode.getPredicate(), (Return) edgeLabel, destinationNode.getPredicate()) == LBool.UNSAT;
	}

	protected boolean isStrongerPredicate(AnnotatedProgramPoint strongerNode, AnnotatedProgramPoint weakerNode) {
		return m_smtManager.isCovered(strongerNode.getPredicate(), weakerNode.getPredicate()) == LBool.UNSAT;
	}
	
	public static String objectReference(Object o) {
		return Integer.toHexString(System.identityHashCode(o));
	}
	

	/**
	 * Debugs all the nodes in a graph.
	 */
	HashSet <AnnotatedProgramPoint> visited = new HashSet<AnnotatedProgramPoint>(); 
	public void debug() {
		visited.clear();
		dfs(m_graphRoot);
	}
	protected boolean debugNode(AnnotatedProgramPoint node) {
		return debugNode(node, "");
	}
	/**
	 * A method used for debugging, it prints all the connections of a given node.
	 * A message can be added to the printed information.
	 * @param node
	 * @param message
	 * @return
	 */
	protected boolean debugNode(AnnotatedProgramPoint node, String message) {
		String display = "";
		/*
		display += String.format("connected To: %s\n", node.getOutgoingNodes());
		display += String.format("connected Fr: %s\n", node.getIncomingNodes());
		*/
//		if (node.m_outgoingReturnCallPreds != null && node.m_outgoingReturnCallPreds.size() > 0) {
//			display += String.format("outGoing: %s\n", node.m_outgoingReturnCallPreds);
//		}
//		if (node.m_nodesThatThisIsReturnCallPredOf != null && node.m_nodesThatThisIsReturnCallPredOf.size() > 0) {
//			display += String.format("inHyperEdges: %s\n", node.m_nodesThatThisIsReturnCallPredOf);
//		}
		if (display.length() > 0) {
			display = String.format("%s\nNode %s:\n", message, node) + display;
			CodeCheckObserver.s_Logger.debug(display);
		}
		return false;
	}
	/**
	 * Depth First Search algorithm that debugs all the nodes in a graph.
	 * @param node : The current Node being explored in the DFS.
	 * @return
	 */
	private boolean dfs(AnnotatedProgramPoint node) {
		if (!visited.contains(node)) {
			visited.add(node);
			debugNode(node);
			AnnotatedProgramPoint[] adj = node.getOutgoingNodes().toArray(new AnnotatedProgramPoint[]{});
			for (AnnotatedProgramPoint child : adj)
				dfs(child);
		}
		return false;
	}
}
