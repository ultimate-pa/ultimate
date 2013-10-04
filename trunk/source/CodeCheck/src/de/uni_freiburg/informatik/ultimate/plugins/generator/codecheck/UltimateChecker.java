package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.AbstractCollection;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;

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
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * UltimateChecker class, implements the model checker Ultimate.
 * 
 * @author Mostafa Mahmoud
 * 
 */
public class UltimateChecker extends CodeChecker {

	HashMap<AnnotatedProgramPoint, HashMap<CodeBlock, AnnotatedProgramPoint>> _pre2stm2post_toConnectIfSat;
	HashMap<AnnotatedProgramPoint, HashMap<AnnotatedProgramPoint, HashMap<Return, AnnotatedProgramPoint>>> _pre2hier2stm2post_toConnectIfSat;
	
	public UltimateChecker(IElement root, SmtManager m_smtManager,
			IPredicate m_truePredicate, IPredicate m_falsePredicate,
			TAPreferences m_taPrefs, RootNode m_originalRoot,
			ImpRootNode m_graphRoot, GraphWriter m_graphWriter, EdgeChecker edgeChecker, PredicateUnifier predicateUnifier) {
		super(root, m_smtManager, m_truePredicate, m_falsePredicate, m_taPrefs,
				m_originalRoot, m_graphRoot, m_graphWriter, edgeChecker, predicateUnifier);
	}

	/**
	 * Given a node and a corresponding interpolants, then split the node with
	 * annotating the interpolants according to the algorithm of ULtimate model
	 * checker. The nodes generated from split are added to the hashMap
	 * nodesClones.
	 * 
	 * @param oldNode
	 * @param interpolant
	 * @return
	 */
	private void splitNode(AnnotatedProgramPoint oldNode, IPredicate predicate) {
		//make two new nodes
		AnnotatedProgramPoint newNode1 = new AnnotatedProgramPoint(oldNode, 
				conjugatePredicates(oldNode.getPredicate(), predicate));
		AnnotatedProgramPoint newNode2 = new AnnotatedProgramPoint(oldNode, conjugatePredicates(
						oldNode.getPredicate(),	negatePredicate(predicate)));
		
		//connect predecessors of old node to new nodes, disconnect them from old node
		AppEdge[] oldInEdges = oldNode.getIncomingEdges().toArray(new AppEdge[]{});
		for (AppEdge oldInEdge : oldInEdges) {
			AnnotatedProgramPoint source = oldInEdge.getSource();
			CodeBlock statement = oldInEdge.getStatement();
			
			//deal with self loops elsewhere
			if (source.equals(oldNode))
				continue;
	
			if (oldInEdge instanceof AppHyperEdge) {
				AnnotatedProgramPoint hier = ((AppHyperEdge) oldInEdge).getHier();
				connectOutgoingReturnIfSat(source, hier, (Return) statement, newNode1);
				connectOutgoingReturnIfSat(source, hier, (Return) statement, newNode2);
			} else {
				connectOutgoingIfSat(source, statement, newNode1);
				connectOutgoingIfSat(source, statement, newNode2);
			}
			
			oldInEdge.disconnect();
		}
		
		//connect successors of old node to new nodes, disconnect them from old node
		AppEdge[] oldOutEdges = oldNode.getOutgoingEdges().toArray(new AppEdge[]{});
		for (AppEdge oldOutEdge : oldOutEdges) {
			AnnotatedProgramPoint target = oldOutEdge.getTarget();
			CodeBlock statement = oldOutEdge.getStatement();
			
			//deal with self loops elsewhere
			if (target.equals(oldNode))
				continue;
			
			if (oldOutEdge instanceof AppHyperEdge) {
				AnnotatedProgramPoint hier = ((AppHyperEdge) oldOutEdge).getHier();
				connectOutgoingReturnIfSat(newNode1, hier, (Return) statement, target);
				connectOutgoingReturnIfSat(newNode2, hier, (Return) statement, target);
			} else {
				connectOutgoingIfSat(newNode1, statement, target);
				connectOutgoingIfSat(newNode2, statement, target);
			}
			
			oldOutEdge.disconnect();
		}
		
		//deal with self loops
		for (AppEdge oldOutEdge : oldOutEdges) {
			AnnotatedProgramPoint target = oldOutEdge.getTarget();
			CodeBlock statement = oldOutEdge.getStatement();
			
			//already dealt with non self loops and disconnected those edges
			if (target == null)
				continue;		
			
			if (oldOutEdge instanceof AppHyperEdge) {
				AnnotatedProgramPoint hier = ((AppHyperEdge) oldOutEdge).getHier();
				connectOutgoingReturnIfSat(newNode1, hier, (Return) statement, newNode1);
				connectOutgoingReturnIfSat(newNode1, hier, (Return) statement, newNode2);
				connectOutgoingReturnIfSat(newNode2, hier, (Return) statement, newNode1);
				connectOutgoingReturnIfSat(newNode2, hier, (Return) statement, newNode2);
			} else {
				connectOutgoingIfSat(newNode1, statement, newNode1);
				connectOutgoingIfSat(newNode1, statement, newNode2);
				connectOutgoingIfSat(newNode2, statement, newNode1);
				connectOutgoingIfSat(newNode2, statement, newNode2);
			}
			
			oldOutEdge.disconnect();
		}
		
		//duplicate outgoing hyperedges
		AppHyperEdge[] oldOutHypEdges = oldNode.getOutgoingHyperEdges().toArray(new AppHyperEdge[]{});
		for (AppHyperEdge oldOutHypEdge : oldOutHypEdges) {
			AnnotatedProgramPoint source = oldOutHypEdge.getSource();
			AnnotatedProgramPoint target = oldOutHypEdge.getTarget();
			Return statement = (Return) oldOutHypEdge.getStatement();
			
			connectOutgoingReturnIfSat(source, newNode1, statement, target);
			connectOutgoingReturnIfSat(source, newNode2, statement, target);
			
			oldOutHypEdge.disconnect();
		}
	}
	
	/**
	 * Given an error trace with the corresponding interpolants, then it
	 * modifies the graph accordingly.
	 */
	public boolean codeCheck(
			NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun,
			IPredicate[] interpolants, AnnotatedProgramPoint procedureRoot) {

		// Debug The Error Trace and the corresponding list of interpolants.
		AnnotatedProgramPoint[] nodes = errorRun.getStateSequence().toArray(
				new AnnotatedProgramPoint[0]);
		ArrayList<AnnotatedProgramPoint> errorTraceDBG = new ArrayList<AnnotatedProgramPoint>();
		Collections.addAll(errorTraceDBG, nodes);
		CodeCheckObserver.s_Logger.debug(String.format("Error: %s\n",
				errorTraceDBG));

		ArrayList<IPredicate> interpolantsDBG = new ArrayList<IPredicate>();
		Collections.addAll(interpolantsDBG, interpolants);
		CodeCheckObserver.s_Logger.debug(String.format("Inters: %s\n",
				interpolantsDBG));
		
		

		for (int i = 0; i < interpolants.length; i++) {
//			_pre2stm2post_toConnectIfSat = 
//					new HashMap<AnnotatedProgramPoint, 
//					HashMap<CodeBlock,AnnotatedProgramPoint>>();
//			_pre2hier2stm2post_toConnectIfSat = 
//					new HashMap<AnnotatedProgramPoint, 
//					HashMap<AnnotatedProgramPoint,
//					HashMap<Return,AnnotatedProgramPoint>>>();
			splitNode(nodes[i + 1], interpolants[i]);
//			makeConnections();
		} 
		
		return true;
	}
	
	private void makeConnections() {
		for (Entry<AnnotatedProgramPoint, HashMap<CodeBlock, AnnotatedProgramPoint>> pre2  
				: _pre2stm2post_toConnectIfSat.entrySet()) 
			for (Entry<CodeBlock, AnnotatedProgramPoint> stm2 
					: pre2.getValue().entrySet()) 
				if (isSatEdge(pre2.getKey(), stm2.getKey(), stm2.getValue())) 
					pre2.getKey().connectOutgoing(stm2.getKey(), stm2.getValue());
		
		for (Entry<AnnotatedProgramPoint, HashMap<AnnotatedProgramPoint, HashMap<Return, AnnotatedProgramPoint>>> pre2
				: _pre2hier2stm2post_toConnectIfSat.entrySet())
			for (Entry<AnnotatedProgramPoint, HashMap<Return, AnnotatedProgramPoint>> hier2  
					: pre2.getValue().entrySet()) 
				for (Entry<Return, AnnotatedProgramPoint> stm2 
						: hier2.getValue().entrySet()) 
					if (isSatRetEdge(pre2.getKey(), hier2.getKey(), stm2.getKey(), stm2.getValue())) 
						pre2.getKey().connectOutgoingReturn(hier2.getKey(), stm2.getKey(), stm2.getValue());	
	}

		/**
	 * Check if an edge between two AnnotatedProgramPoints is satisfiable or not, works with
	 * the cases if the edge is a normal edge or a call edge.
	 * @param sourceNode
	 * @param edgeLabel
	 * @param destinationNode
	 * @return
	 */
	protected boolean isSatEdge(AnnotatedProgramPoint sourceNode, CodeBlock edgeLabel,
			AnnotatedProgramPoint destinationNode) {
		if (edgeLabel instanceof DummyCodeBlock)
			return false;
//		System.out.print(".");
		
		if (edgeLabel instanceof Call) 
			return m_smtManager.isInductiveCall(sourceNode.getPredicate(), (Call) edgeLabel, negatePredicate(destinationNode.getPredicate())) != LBool.UNSAT;
		
		return m_smtManager.isInductive(sourceNode.getPredicate(), edgeLabel, negatePredicate(destinationNode.getPredicate())) != LBool.UNSAT;
	}
	
	/**
	 * Check if a return edge between two AnnotatedProgramPoints is satisfiable or not.
	 * @param sourceNode
	 * @param edgeLabel
	 * @param destinationNode
	 * @param callNode
	 * @return
	 */
	protected boolean isSatRetEdge(AnnotatedProgramPoint sourceNode, AnnotatedProgramPoint callNode, Return edgeLabel,
			AnnotatedProgramPoint destinationNode) {
//		System.out.print(".");
		return m_smtManager.isInductiveReturn(sourceNode.getPredicate(), 
				callNode.getPredicate(), 
				(Return) edgeLabel, 
				negatePredicate(destinationNode.getPredicate())) != LBool.UNSAT;
	}
	
	protected void connectOutgoingIfSat(AnnotatedProgramPoint source,
			CodeBlock statement, AnnotatedProgramPoint target) {
//		if (_pre2stm2post_toConnectIfSat.get(source) == null)
//			_pre2stm2post_toConnectIfSat.put(source, new HashMap<CodeBlock, AnnotatedProgramPoint>());
//		_pre2stm2post_toConnectIfSat.get(source).put(statement, target);
		
		if (isSatEdge(source, statement, target))
			source.connectOutgoing(statement, target);
	}

	protected void connectOutgoingReturnIfSat(AnnotatedProgramPoint source,
			AnnotatedProgramPoint hier, Return statement,
			AnnotatedProgramPoint target) {
//		if (_pre2hier2stm2post_toConnectIfSat.get(source) == null)
//			_pre2hier2stm2post_toConnectIfSat.put(source, new HashMap<AnnotatedProgramPoint, HashMap<Return,AnnotatedProgramPoint>>());
//		if (_pre2hier2stm2post_toConnectIfSat.get(source).get(hier) == null)
//			_pre2hier2stm2post_toConnectIfSat.get(source).put(hier, new HashMap<Return, AnnotatedProgramPoint>());
//		_pre2hier2stm2post_toConnectIfSat.get(source).get(hier).put(statement, target);
		
		if (isSatRetEdge(source, hier, statement, target))
			source.connectOutgoingReturn(hier, statement, target);
	}	
}
