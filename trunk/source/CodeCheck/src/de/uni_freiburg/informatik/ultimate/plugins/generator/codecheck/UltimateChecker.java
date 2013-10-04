package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.AbstractCollection;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.model.IElement;
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
	
//	private boolean hiersHaveReturnPredSetCorrect(
//			AbstractCollection<AnnotatedProgramPoint> possibleReturnPreds) {
//		boolean result = true;
//		for (AnnotatedProgramPoint node : possibleReturnPreds)
//			for (AnnotatedProgramPoint hier : node.getOutgoingReturnCallPreds())
//				if (hier != null)
//					result &= hier.getNodesThatThisIsReturnCallPredOf()
//							.contains(node);
//		if (!result)
//			_graphWriter.writeGraphAsImage(m_graphRoot, "graph_err");
//		return result;
//	}

//	private boolean listsAreOfEqualSize(AnnotatedProgramPoint[][] newNodes,
//			int interpolantsCount) {
//		boolean result = true;
//		for (int i = 0; i < interpolantsCount; ++i) {
//			for (AnnotatedProgramPoint node : newNodes[i]) {
//				if (node != null) {
//					result &= node.m_outgoingReturnCallPreds.size() == node
//							.getOutgoingNodes().size()
//							&& node.getOutgoingNodes().size() == node
//									.getOutgoingEdgeLabels().size();
//				}
//			}
//		}
//		return result;
//	}



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
//			splitNode(nodes[i + 1], new IPredicate[] { interpolants[i] });
			splitNode(nodes[i + 1], interpolants[i]);
		}
		return true;

		// HashMap <AnnotatedProgramPoint, HashSet <AnnotatedProgramPoint>>
		// nodesClones = new HashMap <AnnotatedProgramPoint, HashSet
		// <AnnotatedProgramPoint>>();
		// HashMap <AnnotatedProgramPoint, HashSet <IPredicate>> map = new
		// HashMap <AnnotatedProgramPoint, HashSet <IPredicate>>();
		//
		//
		// for (int i = 0; i < interpolants.length; ++i) {
		// if (!map.containsKey(nodes[i + 1])) {
		// map.put(nodes[i + 1], new HashSet<IPredicate>());
		// }
		// map.get(nodes[i + 1]).add(interpolants[i]);
		// }
		// // Split each node with the corresponding interpolant(s) in the error
		// trace.
		// for (AnnotatedProgramPoint node : map.keySet()) {
		// if (node == procedureRoot) {
		// map.get(node).add(m_truePredicate);
		// }
		// splitNode(node, map.get(node).toArray(new IPredicate[]{}),
		// nodesClones);
		// }
		// return true;
	}
}
