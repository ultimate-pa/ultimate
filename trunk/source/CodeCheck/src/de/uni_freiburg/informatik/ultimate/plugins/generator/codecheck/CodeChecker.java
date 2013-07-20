package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.TermVarsProc;


public abstract class CodeChecker {


	public RootNode m_originalRoot;
	public TAPreferences m_taPrefs;
	public SmtManager m_smtManager;
	public ImpRootNode m_graphRoot;

	public IPredicate m_truePredicate;
	public IPredicate m_falsePredicate;
	
	public CodeChecker(IElement root, SmtManager m_smtManager, IPredicate m_truePredicate, IPredicate m_falsePredicate, TAPreferences m_taPrefs, RootNode m_originalRoot, ImpRootNode m_graphRoot) {
		this.m_smtManager = m_smtManager;
		this.m_truePredicate = m_truePredicate;
		this.m_falsePredicate = m_falsePredicate;
		this.m_taPrefs = m_taPrefs;
		this.m_originalRoot = m_originalRoot;
		this.m_graphRoot = m_graphRoot;
	}
	
	public abstract boolean codeCheck(AnnotatedProgramPoint[] nodes, IPredicate[] interpolants, AnnotatedProgramPoint procedureRoot);

	
	protected IPredicate conjugatePredicates(IPredicate a, IPredicate b) {
		TermVarsProc tvp = m_smtManager.and(a, b);
		return m_smtManager.newPredicate(tvp.getFormula(), tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
	}
	
	protected IPredicate negatePredicate(IPredicate a) {
		TermVarsProc tvp = m_smtManager.not(a);
		return m_smtManager.newPredicate(tvp.getFormula(), tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
	}

	protected boolean isSatEdge(AnnotatedProgramPoint sourceNode, CodeBlock edgeLabel,
			AnnotatedProgramPoint destinationNode) {
		if (edgeLabel instanceof DummyCodeBlock)
			return false;
		System.out.print(".");
		
		if (edgeLabel instanceof Call) 
			return m_smtManager.isInductiveCall(sourceNode.getPredicate(), (Call) edgeLabel, negatePredicate(destinationNode.getPredicate())) != LBool.UNSAT;
		
		return m_smtManager.isInductive(sourceNode.getPredicate(), edgeLabel, negatePredicate(destinationNode.getPredicate())) != LBool.UNSAT;
	}
	
	protected boolean isSatRetEdge(AnnotatedProgramPoint sourceNode, Return edgeLabel,
			AnnotatedProgramPoint destinationNode, AnnotatedProgramPoint callNode) {
		System.out.print(".");
		return m_smtManager.isInductiveReturn(sourceNode.getPredicate(), callNode.getPredicate(), (Return) edgeLabel, negatePredicate(destinationNode.getPredicate())) != LBool.UNSAT;
	}
	
	protected boolean isValidEdge(AnnotatedProgramPoint sourceNode, CodeBlock edgeLabel,
			AnnotatedProgramPoint destinationNode) {
		if (edgeLabel instanceof DummyCodeBlock)
			return false;
		System.out.print(".");
		
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
	
	
	HashSet <AnnotatedProgramPoint> visited = new HashSet<AnnotatedProgramPoint>(); 
	public void debug() {
		visited.clear();
		dfs(m_graphRoot);
	}
	private boolean dfs(AnnotatedProgramPoint node) {
		if (!visited.contains(node)) {
			visited.add(node);
			CodeCheckObserver.s_Logger.debug(String.format("Node: %s:\noutGoing: %s\ninHyperEdges: %s\n", node, node.m_outgoingReturnAppToCallPreds, node.m_ingoingReturnAppToCallPreds));
			AnnotatedProgramPoint[] adj = node.getOutgoingNodes().toArray(new AnnotatedProgramPoint[]{});
			for (int i = 0; i < adj.length; ++i) {
				dfs(adj[i]);
			}
		}
		return false;
	}
}
