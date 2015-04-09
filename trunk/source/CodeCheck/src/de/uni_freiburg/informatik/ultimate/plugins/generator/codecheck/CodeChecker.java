package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.HashMap;
import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AnnotatedProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.ImpRootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.util.relation.IsContained;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap4;

public abstract class CodeChecker {

	protected RootNode m_originalRoot;
	protected TAPreferences m_taPrefs;
	protected SmtManager m_smtManager;
	protected ImpRootNode m_graphRoot;


	protected IHoareTripleChecker _edgeChecker;
	protected PredicateUnifier m_predicateUnifier;

	/*
	 * Maps for storing edge check results. Not that in case of ImpulseChecker these really are valid, not sat, triples.
	 * TODO: either change name, make duplicates for ImpulseChecker, or modify ImpulseChecker such that those are really sat triples.
	 */
	protected NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> _satTriples;
	protected NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> _unsatTriples;
	protected NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained> _satQuadruples;
	protected NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained> _unsatQuadruples;

	// stats
	protected int memoizationHitsSat = 0;
	protected int memoizationHitsUnsat = 0;
	protected int memoizationReturnHitsSat = 0;
	protected int memoizationReturnHitsUnsat = 0;

	protected GraphWriter _graphWriter;

	public CodeChecker(IElement root, SmtManager smtManager, TAPreferences taPrefs, RootNode originalRoot, ImpRootNode graphRoot, GraphWriter graphWriter,
			IHoareTripleChecker edgeChecker, PredicateUnifier predicateUnifier, Logger logger) {
		mLogger = logger;
		this.m_smtManager = smtManager;
		this.m_taPrefs = taPrefs;
		this.m_originalRoot = originalRoot;
		this.m_graphRoot = graphRoot;

		this._edgeChecker = edgeChecker;
		this.m_predicateUnifier = predicateUnifier;

		this._graphWriter = graphWriter;
	}

	public abstract boolean codeCheck(NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun, IPredicate[] interpolants,
			AnnotatedProgramPoint procedureRoot);

	public abstract boolean codeCheck(NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun, IPredicate[] interpolants,
			AnnotatedProgramPoint procedureRoot,
			NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> satTriples,
			NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> unsatTriples);

	public abstract boolean codeCheck(NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun, IPredicate[] interpolants,
			AnnotatedProgramPoint procedureRoot,
			NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> satTriples,
			NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> unsatTriples,
			NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained> satQuadruples,
			NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained> unsatQuadruples);

	/**
	 * Given 2 predicates, return a predicate which is the conjunction of both.
	 * 
	 * @param a
	 *            : The first Predicate.
	 * @param b
	 *            : The second Predicate.
	 */
	protected IPredicate conjugatePredicates(IPredicate a, IPredicate b) {
		TermVarsProc tvp = m_smtManager.and(a, b);
		return m_predicateUnifier.getOrConstructPredicate(tvp);
	}

	/**
	 * Given a predicate, return a predicate which is the negation of it.
	 * 
	 * @param a
	 *            : The Predicate.
	 */
	protected IPredicate negatePredicate(IPredicate a) {
		TermVarsProc tvp = m_smtManager.not(a);
		return m_predicateUnifier.getOrConstructPredicate(tvp);
	}

	/**
	 * Given a predicate, return a predicate which is the negation of it, not
	 * showing it to the PredicateUnifier
	 * 
	 * @param a
	 *            : The Predicate.
	 */
	protected IPredicate negatePredicateNoPU(IPredicate a) {
		TermVarsProc tvp = m_smtManager.not(a);
		return m_smtManager.newPredicate(tvp.getFormula(), tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
	}


	public static String objectReference(Object o) {
		return Integer.toHexString(System.identityHashCode(o));
	}

	/**
	 * Debugs all the nodes in a graph.
	 */
	HashSet<AnnotatedProgramPoint> visited = new HashSet<AnnotatedProgramPoint>();
	protected final Logger mLogger;

	public void debug() {
		visited.clear();
		dfs(m_graphRoot);
	}

	protected boolean debugNode(AnnotatedProgramPoint node) {
		return debugNode(node, "");
	}

	/**
	 * A method used for debugging, it prints all the connections of a given
	 * node. A message can be added to the printed information.
	 * 
	 * @param node
	 * @param message
	 * @return
	 */
	protected boolean debugNode(AnnotatedProgramPoint node, String message) {
		String display = "";
		/*
		 * display += String.format("connected To: %s\n",
		 * node.getOutgoingNodes()); display +=
		 * String.format("connected Fr: %s\n", node.getIncomingNodes());
		 */
		// if (node.m_outgoingReturnCallPreds != null &&
		// node.m_outgoingReturnCallPreds.size() > 0) {
		// display += String.format("outGoing: %s\n",
		// node.m_outgoingReturnCallPreds);
		// }
		// if (node.m_nodesThatThisIsReturnCallPredOf != null &&
		// node.m_nodesThatThisIsReturnCallPredOf.size() > 0) {
		// display += String.format("inHyperEdges: %s\n",
		// node.m_nodesThatThisIsReturnCallPredOf);
		// }
		if (display.length() > 0) {
			display = String.format("%s\nNode %s:\n", message, node) + display;
			mLogger.debug(display);
		}
		return false;
	}

	/**
	 * Depth First Search algorithm that debugs all the nodes in a graph.
	 * 
	 * @param node
	 *            : The current Node being explored in the DFS.
	 * @return
	 */
	private boolean dfs(AnnotatedProgramPoint node) {
		if (!visited.contains(node)) {
			visited.add(node);
			debugNode(node);
			AnnotatedProgramPoint[] adj = node.getOutgoingNodes().toArray(new AnnotatedProgramPoint[] {});
			for (AnnotatedProgramPoint child : adj)
				dfs(child);
		}
		return false;
	}
}
