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
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

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
			ImpRootNode m_graphRoot, GraphWriter m_graphWriter) {
		super(root, m_smtManager, m_truePredicate, m_falsePredicate, m_taPrefs,
				m_originalRoot, m_graphRoot, m_graphWriter);
	}

	/**
	 * Given a node and a corresponding interpolants, then split the node with
	 * annotating the interpolants according to the algorithm of ULtimate model
	 * checker. The nodes generated from split are added to the hashMap
	 * nodesClones.
	 * 
	 * @param oldNode
	 * @param interpolant
	 * @param nodesClones
	 * @return
	 */
//	private boolean splitNode(AnnotatedProgramPoint oldNode,
//			IPredicate[] interpolant) {
//		debugNode(oldNode, oldNode + " will be split");
//
//		_graphWriter.writeGraphAsImage(m_graphRoot, String.format(
//				"graph_%s_beginSplit_%s", _graphWriter._graphCounter, oldNode
//						.toString().substring(0, 5)));
//		assert hiersHaveReturnPredSetCorrect((AbstractCollection<AnnotatedProgramPoint>) Collections
//				.singleton(oldNode));
//
//		HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>> nodesClones = new HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>>();
//
//		// Create the new nodes with the conjugations of the interpolants.
//		int interpolantsCount = interpolant.length;
//		AnnotatedProgramPoint[][] newNodes = new AnnotatedProgramPoint[interpolantsCount][2];
//		for (int i = 0; i < interpolantsCount; ++i) {
//			newNodes[i] = new AnnotatedProgramPoint[] {
//					new AnnotatedProgramPoint(oldNode, conjugatePredicates(
//							oldNode.getPredicate(), interpolant[i])),
//					new AnnotatedProgramPoint(oldNode, conjugatePredicates(
//							oldNode.getPredicate(),
//							negatePredicate(interpolant[i]))) };
//		}
//
//		 AnnotatedProgramPoint[] predecessorNodes = oldNode.getIncomingNodes().toArray(new AnnotatedProgramPoint[]{});
//
//		// Connect the predecessors of the oldNode to the new Nodes, then remove
//		// the original node.
//		for (AnnotatedProgramPoint predecessorNode : predecessorNodes) {
//			// for (int oldNodeIncomingIndex = 0; oldNodeIncomingIndex <
//			// oldNode.getIncomingNodes().size(); oldNodeIncomingIndex++) {
//			// AnnotatedProgramPoint predecessorNode =
//			// oldNode.getIncomingNodes().get(oldNodeIncomingIndex);
//			if (predecessorNode != oldNode) {
//				for (int predNodeOutgoingIndex = predecessorNode
//						.getOutgoingNodes().size() - 1; predNodeOutgoingIndex >= 0; predNodeOutgoingIndex--) {
//					if (predecessorNode.getOutgoingNodes()
//							.get(predNodeOutgoingIndex).equals(oldNode)) {
//						CodeBlock label = predecessorNode
//								.getOutgoingEdgeLabels().get(
//										predNodeOutgoingIndex);
//						boolean isReturn = label instanceof Return;
//						for (int i = 0; i < interpolantsCount; ++i) {
//							for (AnnotatedProgramPoint newNode : newNodes[i]) {
//								if (isReturn) {
//									AnnotatedProgramPoint callPred = predecessorNode
//											.getOutgoingReturnCallPreds().get(
//													predNodeOutgoingIndex);
//									// predecessorNode.getOutgoingNodes().indexOf(oldNode));
//									if (isSatRetEdge(predecessorNode,
//											(Return) label, newNode, callPred))
//										predecessorNode
//												.connectOutgoingWithReturn(
//														newNode,
//														(Return) label,
//														callPred);
//								} else {
//									if (isSatEdge(predecessorNode, label,
//											newNode))
//										predecessorNode.connectOutgoing(
//												newNode, label);
//								}
//							}
//						}
//						predecessorNode
//								.disconnectOutgoing(predNodeOutgoingIndex);
//					}
//				}
//			}
//		}
//
//		// _graphWriter.writeGraphAsImage(m_graphRoot,
//		// String.format("graph_%s_splitPredsConnected_%s",
//		// _graphWriter._graphCounter, oldNode.toString().substring(0, 5)));
//		assert hiersHaveReturnPredSetCorrect((AbstractCollection<AnnotatedProgramPoint>) Collections
//				.singleton(oldNode));
//		assert listsAreOfEqualSize(newNodes, interpolantsCount);
//		assert oldNode.m_outgoingReturnCallPreds.size() == oldNode
//				.getOutgoingNodes().size()
//				&& oldNode.getOutgoingNodes().size() == oldNode
//						.getOutgoingEdgeLabels().size();
//
//		 AnnotatedProgramPoint[] successorNodes = oldNode.getOutgoingNodes().toArray(new AnnotatedProgramPoint[]{});
//
//		// Connect The new Nodes to the successors of the old node.
//		 for (AnnotatedProgramPoint successorNode : successorNodes) {
////		for (int oldNodeSuccIndex = oldNode.getOutgoingNodes().size() - 1; oldNodeSuccIndex >= 0; oldNodeSuccIndex--) {
////			AnnotatedProgramPoint successorNode = oldNode.getOutgoingNodes().get(oldNodeSuccIndex);
//			int oldNodeSuccIndex = oldNode.getOutgoingNodes().indexOf(successorNode);
//			if (successorNode != oldNode) {
//				CodeBlock label = oldNode.getOutgoingEdgeLabels().get(oldNodeSuccIndex);
//				boolean isReturn = label instanceof Return;
//				for (int i = 0; i < interpolantsCount; ++i) {
//					for (AnnotatedProgramPoint newNode : newNodes[i]) {
//						if (isReturn) {
//							AnnotatedProgramPoint callPred = oldNode.getOutgoingReturnCallPreds().get(oldNodeSuccIndex);
////											oldNode.getOutgoingNodes().indexOf(successorNode));
//							if (isSatRetEdge(newNode, (Return) label, successorNode, callPred))
//								newNode.connectOutgoingWithReturn(successorNode, (Return) label, callPred);
//						} else {
//							if (isSatEdge(newNode, label, successorNode))
//								newNode.connectOutgoing(successorNode, label);
//						}
//					}
//				}
//				oldNode.disconnectOutgoing(oldNodeSuccIndex);
//			}
//		}
//
//		// _graphWriter.writeGraphAsImage(m_graphRoot,
//		// String.format("graph_%s_splitSuccsConnected_%s",
//		// _graphWriter._graphCounter, oldNode.toString().substring(0, 5)));
//		assert hiersHaveReturnPredSetCorrect((AbstractCollection<AnnotatedProgramPoint>) Collections
//				.singleton(oldNode));
//		assert listsAreOfEqualSize(newNodes, interpolantsCount);
//		assert oldNode.m_outgoingReturnCallPreds.size() == oldNode
//				.getOutgoingNodes().size()
//				&& oldNode.getOutgoingNodes().size() == oldNode
//						.getOutgoingEdgeLabels().size();
//
//		boolean selfLoop = oldNode.getSuccessors().contains(oldNode);
//		// Connects the new nodes to each others in case of selfloops in the
//		// original node.
//		if (selfLoop) {
//			// FIXME: Check if complete association required.
//			CodeBlock label = oldNode.getOutgoingEdgeLabel(oldNode);
//			assert (!(label instanceof Return));// might happen and make
//												// problems..
//			for (int i = 0; i < interpolantsCount; ++i) {
//				for (AnnotatedProgramPoint source : newNodes[i]) {
//					for (AnnotatedProgramPoint destination : newNodes[i]) {
//						if (isSatEdge(source, label, destination)) {
//							// source.addOutgoingNode(destination, label);
//							// destination.addIncomingNode(source);
//							source.connectOutgoing(destination, label);
//						}
//					}
//				}
//			}
//		}
//
//		// _graphWriter.writeGraphAsImage(m_graphRoot,
//		// String.format("graph_%s_splitSelfloopsConnected_%s",
//		// _graphWriter._graphCounter, oldNode.toString().substring(0, 5)));
//		assert hiersHaveReturnPredSetCorrect((AbstractCollection<AnnotatedProgramPoint>) Collections
//				.singleton(oldNode));
//		assert listsAreOfEqualSize(newNodes, interpolantsCount);
//		assert oldNode.m_outgoingReturnCallPreds.size() == oldNode
//				.getOutgoingNodes().size()
//				&& oldNode.getOutgoingNodes().size() == oldNode
//						.getOutgoingEdgeLabels().size();
//
//		// Add the new Nodes to the HashMap.
//		nodesClones.put(oldNode, new HashSet<AnnotatedProgramPoint>());
//		for (int i = 0; i < interpolantsCount; ++i) {
//			for (AnnotatedProgramPoint node : newNodes[i]) {
//				if (node != null) {
//					nodesClones.get(oldNode).add(node);
//				}
//			}
//		}
//
//		// In case of being a call node for some procedure, then edit update all
//		// the corresponding hyperEdges pointing to the oldNode as a call Node.
//		// new try
//		AnnotatedProgramPoint[] returnPredecessorsWithThisCallPredecessor = oldNode
//				.getNodesThatThisIsReturnCallPredOf().toArray(
//						new AnnotatedProgramPoint[] {});
//
//		for (AnnotatedProgramPoint returnPredecessorWithThisCallPredecessor : returnPredecessorsWithThisCallPredecessor) {
//			_graphWriter.writeGraphAsImage(m_graphRoot, "graph_"
//					+ _graphWriter._graphCounter + "_rcpSplit-1BeforeEdgeDup_"
//					+ oldNode.toString());
//
//			for (int i = returnPredecessorWithThisCallPredecessor
//					.getOutgoingReturnCallPreds().size() - 1; i >= 0; i--) {// downwards
//																			// is
//																			// important!!!
//				if (returnPredecessorWithThisCallPredecessor
//						.getOutgoingReturnCallPreds().get(i).equals(oldNode)) {
//					AnnotatedProgramPoint returnDest = returnPredecessorWithThisCallPredecessor
//							.getOutgoingNodes().get(i);
//					Return returnEdge = (Return) returnPredecessorWithThisCallPredecessor
//							.getOutgoingEdgeLabels().get(i);
//					// remove old return edge with old callpred
//					returnPredecessorWithThisCallPredecessor
//							.disconnectOutgoing(i);
//					// make new return edges with new callpreds
//					for (AnnotatedProgramPoint newCallPred : nodesClones
//							.get(oldNode)) {
//						if (isSatRetEdge(
//								returnPredecessorWithThisCallPredecessor,
//								returnEdge, returnDest, newCallPred))
//							returnPredecessorWithThisCallPredecessor
//									.connectOutgoingWithReturn(returnDest,
//											returnEdge, newCallPred);
//					}
//				}
//			}
//			_graphWriter.writeGraphAsImage(m_graphRoot, "graph_"
//					+ _graphWriter._graphCounter + "_rcpSplit-2AfterEdgeDup_"
//					+ oldNode.toString());
//		}
//
//		// _graphWriter.writeGraphAsImage(m_graphRoot,
//		// String.format("graph_%s_splitReturnEdgesDuplicated_%s",
//		// _graphWriter._graphCounter, oldNode.toString().substring(0, 5)));
//		// old
//		// HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>>
//		// referredHEs = oldNode.m_ingoingReturnCallPreds;
//		// AnnotatedProgramPoint[] preRets = referredHEs.keySet().toArray(new
//		// AnnotatedProgramPoint[]{});
//		// for (AnnotatedProgramPoint preRet : preRets) {
//		// AnnotatedProgramPoint[] rets = referredHEs.get(preRet).toArray(new
//		// AnnotatedProgramPoint[]{});
//		// for (AnnotatedProgramPoint ret : rets) {
//		// preRet.removeOutgoingReturnCallPred(ret, oldNode);
//		// for (AnnotatedProgramPoint newNode : nodesClones.get(oldNode)) {
//		// //CodeCheckObserver.s_Logger.debug(String.format("%s ~~~> %s; %s",
//		// preRet, ret, newNode));
//		// CodeBlock label = preRet.getOutgoingEdgeLabel(ret);
//		// if (isSatRetEdge(preRet, (Return) label, ret, newNode)) {
//		// //CodeCheckObserver.s_Logger.debug("Satisfiable");
//		// preRet.addOutGoingReturnCallPred(ret, newNode);
//		// } else {
//		// //CodeCheckObserver.s_Logger.debug("Not Satisfiable");
//		// }
//		//
//		// }
//		// }
//		// }
//		// Remove any unnecessary edges.
//		// new
//		for (int i = 0; i < interpolantsCount; ++i) {
//			for (AnnotatedProgramPoint newNode : newNodes[i]) {
//
//				for (int j = 0; j < newNode.getOutgoingNodes().size(); j++) {
//					if (newNode.getOutgoingReturnCallPreds().get(j) != null) {
//						Return retLabel = (Return) newNode
//								.getOutgoingEdgeLabels().get(j);
//						AnnotatedProgramPoint returnSuccessor = newNode
//								.getOutgoingNodes().get(j);
//						AnnotatedProgramPoint returnCallPred = newNode
//								.getOutgoingReturnCallPreds().get(j);
//						if (!isSatRetEdge(newNode, retLabel, returnSuccessor,
//								returnCallPred)) {
//							newNode.disconnectOutgoing(j);
//							assert false;// does this really happen? i thought
//											// we are not creating any return
//											// edges that are unsat
//						}
//					}
//				}
//
//			}
//		}
//		// old
//		// for (int i = 0; i < interpolantsCount; ++i) {
//		// for (AnnotatedProgramPoint newNode : newNodes[i]) {
//		// AnnotatedProgramPoint[] retNodes =
//		// newNode.m_outgoingReturnCallPreds.keySet().toArray(new
//		// AnnotatedProgramPoint[]{});
//		// for (AnnotatedProgramPoint retNode : retNodes) {
//		// CodeBlock label = newNode.getOutgoingEdgeLabel(retNode);
//		// if (label == null) {
//		// continue;
//		// }
//		// AnnotatedProgramPoint[] callNodes =
//		// newNode.getCallPredsOfOutgoingReturnTarget(retNode).toArray(new
//		// AnnotatedProgramPoint[]{}) ;
//		// for (AnnotatedProgramPoint callNode : callNodes) {
//		// if (!isSatRetEdge(newNode, (Return) label, retNode, callNode)) {
//		// newNode.removeOutgoingReturnCallPred(retNode, callNode);
//		// }
//		// }
//		// }
//		// }
//		// }
//
//		for (AnnotatedProgramPoint newNode : nodesClones.get(oldNode))
//			debugNode(newNode, "A node copy of " + oldNode);
//
//		_graphWriter.writeGraphAsImage(m_graphRoot, String.format(
//				"graph_%s_endSplit_%s", _graphWriter._graphCounter, oldNode
//						.toString().substring(0, 5)));
//		assert hiersHaveReturnPredSetCorrect((AbstractCollection<AnnotatedProgramPoint>) Collections
//				.singleton(oldNode));
//		assert hiersHaveReturnPredSetCorrect(nodesClones.get(oldNode));
//
//		return true;
//	}

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
		
		//manage self loops
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
