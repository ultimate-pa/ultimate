package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

/**
 * UltimateChecker class, implements the model checker Ultimate.
 * @author Mostafa Mahmoud
 *
 */
public class UltimateChecker extends CodeChecker {
	
	
	public UltimateChecker(IElement root, SmtManager m_smtManager, IPredicate m_truePredicate, IPredicate m_falsePredicate, TAPreferences m_taPrefs, RootNode m_originalRoot, ImpRootNode m_graphRoot) {
		super(root, m_smtManager, m_truePredicate, m_falsePredicate, m_taPrefs, m_originalRoot, m_graphRoot);
		// TODO Auto-generated constructor stub
	}
	
	/**
	 * Given a node and a corresponding interpolants, then split the node with annotating the interpolants
	 * according to the algorithm of ULtimate model checker. The nodes generated from split are added to 
	 * the hashMap nodesClones. 
	 * @param oldNode
	 * @param interpolant
	 * @param nodesClones
	 * @return
	 */
	private boolean splitNode(AnnotatedProgramPoint oldNode, IPredicate[] interpolant, HashMap <AnnotatedProgramPoint, HashSet <AnnotatedProgramPoint>> nodesClones) {
		debugNode(oldNode, oldNode + " will be split");
		
		// Create the new nodes with the conjugations of the interpolants.
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
		
		// Connect the predecessors of the oldNode to the new Nodes, then remove the original node.
		for (AnnotatedProgramPoint predecessorNode : predecessorNodes) {
			if (predecessorNode != oldNode) {
				CodeBlock label = predecessorNode.getOutgoingEdgeLabel(oldNode);
				boolean isReturn = label instanceof Return;
				for (int i = 0; i < interpolantsCount; ++i) {
					for (AnnotatedProgramPoint newNode : newNodes[i]) {
						if (isReturn) {
							AnnotatedProgramPoint[] hyperEdges = predecessorNode.getCallPredsOfOutgoingReturnTarget(oldNode).toArray(new AnnotatedProgramPoint[]{});
							
							boolean putEdge = false;
							for (AnnotatedProgramPoint callNode : hyperEdges) {
								if (isSatRetEdge(predecessorNode, (Return) label, newNode, callNode)) {
									if (!putEdge)
										predecessorNode.connectTo(newNode, label);
									putEdge |= true;
									predecessorNode.addOutGoingReturnCallPred(newNode, callNode);
								}
							}
						} else {
							if (isSatEdge(predecessorNode, label, newNode)) {
								predecessorNode.connectTo(newNode, label);
							}
						}
					}
				}
				predecessorNode.disconnectFrom(oldNode);
			}
		}
		
		// Connect The new Nodes to the successors of the old node.
		for (AnnotatedProgramPoint successorNode : successorNodes) {
			if (successorNode != oldNode) {
				CodeBlock label = oldNode.getOutgoingEdgeLabel(successorNode);
				boolean isReturn = label instanceof Return;
				for (int i = 0; i < interpolantsCount; ++i) {
					for (AnnotatedProgramPoint newNode : newNodes[i]) {
						if (isReturn) {
							AnnotatedProgramPoint[] hyperEdges = oldNode.getCallPredsOfOutgoingReturnTarget(successorNode).toArray(new AnnotatedProgramPoint[]{});
							
							boolean putEdge = false;
							for (AnnotatedProgramPoint callNode : hyperEdges) {
								if (isSatRetEdge(newNode, (Return) label, successorNode, callNode)) {
									if (!putEdge)
										newNode.connectTo(successorNode, label);
									putEdge |= true;
									newNode.addOutGoingReturnCallPred(successorNode, callNode);
								}
							}
						} else {
							if (isSatEdge(newNode, label, successorNode)) {
								newNode.connectTo(successorNode, label);
							}
						}
					}
				}
				oldNode.disconnectFrom(successorNode);
			}
		}
		
		
		boolean selfLoop = oldNode.getSuccessors().contains(oldNode);
		// Connects the new nodes to each others in case of selfloops in the original node.
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
		
		// Add the new Nodes to the HashMap.
		nodesClones.put(oldNode, new HashSet <AnnotatedProgramPoint>());
		for (int i = 0; i < interpolantsCount; ++i) {
			for (AnnotatedProgramPoint node : newNodes[i]) {
				if (node != null) {
					nodesClones.get(oldNode).add(node);
				}
			}
		}
		
		// In case of being a call node for some procedure, then edit update all
		// the corresponding hyperEdges pointing to the oldNode as a call Node.
		HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>> referredHEs = oldNode.m_ingoingReturnAppToCallPreds;
		AnnotatedProgramPoint[] preRets = referredHEs.keySet().toArray(new AnnotatedProgramPoint[]{});
		for (AnnotatedProgramPoint preRet : preRets) {
			AnnotatedProgramPoint[] rets = referredHEs.get(preRet).toArray(new AnnotatedProgramPoint[]{});
			for (AnnotatedProgramPoint ret : rets) {
				preRet.removeOutgoingReturnCallPred(ret, oldNode);
				for (AnnotatedProgramPoint newNode : nodesClones.get(oldNode)) {
					//CodeCheckObserver.s_Logger.debug(String.format("%s ~~~> %s; %s", preRet, ret, newNode));
					CodeBlock label = preRet.getOutgoingEdgeLabel(ret);
					if (isSatRetEdge(preRet, (Return) label, ret, newNode)) {
						//CodeCheckObserver.s_Logger.debug("Satisfiable");
						preRet.addOutGoingReturnCallPred(ret, newNode);
					} else {
						//CodeCheckObserver.s_Logger.debug("Not Satisfiable");
					}
					
				}
			}
		}
		// Remove any unnecessary edges.
		for (int i = 0; i < interpolantsCount; ++i) {
			for (AnnotatedProgramPoint newNode : newNodes[i]) {
				AnnotatedProgramPoint[] retNodes = newNode.m_outgoingReturnAppToCallPreds.keySet().toArray(new AnnotatedProgramPoint[]{});
				for (AnnotatedProgramPoint retNode : retNodes) {
					CodeBlock label = newNode.getOutgoingEdgeLabel(retNode);
					if (label == null) {
						continue;
					}
					AnnotatedProgramPoint[] callNodes = newNode.getCallPredsOfOutgoingReturnTarget(retNode).toArray(new AnnotatedProgramPoint[]{}) ;
					for (AnnotatedProgramPoint callNode : callNodes) {
						if (!isSatRetEdge(newNode, (Return) label, retNode, callNode)) {
							newNode.removeOutgoingReturnCallPred(retNode, callNode);
						}
					}
				}
			}
		}
		for (AnnotatedProgramPoint newNode : nodesClones.get(oldNode))
			debugNode(newNode, "A node copy of " + oldNode);
		
		return true;
	}
	/**
	 * Given an error trace with the corresponding interpolants, then it modifies the graph accordingly.
	 */
	public boolean codeCheck(AnnotatedProgramPoint[] nodes, IPredicate[] interpolants, AnnotatedProgramPoint procedureRoot) {
		
		// Debug The Error Trace and the corresponding list of interpolants.
		ArrayList <AnnotatedProgramPoint> errorTraceDBG = new ArrayList<AnnotatedProgramPoint>();
		Collections.addAll(errorTraceDBG, nodes);
		CodeCheckObserver.s_Logger.debug(String.format("Error: %s\n", errorTraceDBG));
		
		ArrayList <IPredicate> interpolantsDBG = new ArrayList<IPredicate>();
		Collections.addAll(interpolantsDBG, interpolants);
		CodeCheckObserver.s_Logger.debug(String.format("Inters: %s\n", interpolantsDBG));
		
		
		HashMap <AnnotatedProgramPoint, HashSet <AnnotatedProgramPoint>> nodesClones = new HashMap <AnnotatedProgramPoint, HashSet <AnnotatedProgramPoint>>();
		HashMap <AnnotatedProgramPoint, HashSet <IPredicate>> map = new HashMap <AnnotatedProgramPoint, HashSet <IPredicate>>();
		
		
		for (int i = 0; i < interpolants.length; ++i) {
			if (!map.containsKey(nodes[i + 1])) {
				map.put(nodes[i + 1], new HashSet<IPredicate>());
			}
			map.get(nodes[i + 1]).add(interpolants[i]);
		}
		// Split each node with the corresponding interpolant(s) in the error trace.
		for (AnnotatedProgramPoint node : map.keySet()) {
			if (node == procedureRoot) {
				map.get(node).add(m_truePredicate);
			}
			splitNode(node, map.get(node).toArray(new IPredicate[]{}), nodesClones);
		}
		return true;
	}
}
