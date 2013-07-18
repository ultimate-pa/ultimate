package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class UltimateChecker extends CodeChecker {
	
	
	public UltimateChecker(IElement root, SmtManager m_smtManager, IPredicate m_truePredicate, IPredicate m_falsePredicate, TAPreferences m_taPrefs, RootNode m_originalRoot, ImpRootNode m_graphRoot) {
		super(root, m_smtManager, m_falsePredicate, m_falsePredicate, m_taPrefs, m_originalRoot, m_graphRoot);
		// TODO Auto-generated constructor stub
	}
	
	private boolean splitNode(AnnotatedProgramPoint oldNode, IPredicate[] interpolant, HashMap <AnnotatedProgramPoint, ArrayList <AnnotatedProgramPoint>> nodesClones) {
		int interpolantsCount = interpolant.length;
		AnnotatedProgramPoint[][] newNodes = new AnnotatedProgramPoint[interpolantsCount][2];
		for (int i = 0; i < interpolantsCount; ++i) {
			newNodes[i] = new AnnotatedProgramPoint[] {
					new AnnotatedProgramPoint(oldNode, conjugatePredicates(oldNode.getPredicate(), interpolant[i]), true),
					new AnnotatedProgramPoint(oldNode, conjugatePredicates(oldNode.getPredicate(), negatePredicate(interpolant[i])), true)
					};
		}
		
		AnnotatedProgramPoint[] predecessorNodes = oldNode.getIncomingNodes().toArray(new AnnotatedProgramPoint[]{});
		AnnotatedProgramPoint[] successorNodes = oldNode.getOutgoingNodes().toArray(new AnnotatedProgramPoint[]{});
		
		
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
									putEdge |= true;
									predecessorNode.addOutGoingReturnCallPred(newNode, callNode);
								}
							}
							if (putEdge) {
								predecessorNode.connectTo(newNode, label);
							}
						} else {
							if (isSatEdge(predecessorNode, label, newNode)) {
								predecessorNode.connectTo(newNode, label);
							}
						}
					}
				}
				if (isReturn) {
					AnnotatedProgramPoint[] hyperEdges = predecessorNode.getCallPredsOfOutgoingReturnTarget(oldNode).toArray(new AnnotatedProgramPoint[]{});
					for (AnnotatedProgramPoint callNode : hyperEdges) {
						predecessorNode.removeOutgoingReturnCallPred(oldNode, callNode);
					}
				}
				predecessorNode.disconnectFrom(oldNode);
			}
		}

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
									putEdge |= true;
									System.err.println(newNode.addOutGoingReturnCallPred(successorNode, callNode));
								}
							}
							if (putEdge) {
								newNode.connectTo(successorNode, label);
							}
						} else {
							if (isSatEdge(newNode, label, successorNode)) {
								newNode.connectTo(successorNode, label);
							}
						}
					}
				}
				if (isReturn) {
					AnnotatedProgramPoint[] hyperEdges = oldNode.getCallPredsOfOutgoingReturnTarget(successorNode).toArray(new AnnotatedProgramPoint[]{});
					
					for (AnnotatedProgramPoint callNode : hyperEdges) {
						oldNode.removeOutgoingReturnCallPred(successorNode, callNode);
					}
				}
				oldNode.disconnectFrom(successorNode);
			}
		}
		
		
		boolean selfLoop = oldNode.getSuccessors().contains(oldNode);
		
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
		//System.out.println("Splitted node : " + oldNode.toString());
		
		nodesClones.put(oldNode, new ArrayList <AnnotatedProgramPoint>());
		for (int i = 0; i < interpolantsCount; ++i) {
			for (AnnotatedProgramPoint node : newNodes[i]) {
				if (node != null) {
					nodesClones.get(oldNode).add(node);
				}
			}
		}
		
		HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>> referredHEs = oldNode.m_ingoingReturnAppToCallPreds;
		AnnotatedProgramPoint[] preRets = referredHEs.keySet().toArray(new AnnotatedProgramPoint[]{});
		for (AnnotatedProgramPoint preRet : preRets) {
			AnnotatedProgramPoint[] rets = referredHEs.get(preRet).toArray(new AnnotatedProgramPoint[]{});
			for (AnnotatedProgramPoint ret : rets) {
				preRet.removeOutgoingReturnCallPred(ret, oldNode);
				for (AnnotatedProgramPoint newNode : nodesClones.get(oldNode)) {
					preRet.addOutGoingReturnCallPred(ret, newNode);
					/*
					CodeBlock label = preRet.getOutgoingEdgeLabel(ret);
					if (isSatRetEdge(preRet, (Return) label, ret, newNode)) {
					}
					*/
				}
			}
		}
		

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
		
		return true;
	}
	
	public boolean codeCheck(AnnotatedProgramPoint[] nodes, IPredicate[] interpolants, AnnotatedProgramPoint procedureRoot) {

		ArrayList <AnnotatedProgramPoint> errorTraceDBG = new ArrayList<AnnotatedProgramPoint>();
		Collections.addAll(errorTraceDBG, nodes);
		CodeCheckObserver.s_Logger.debug(String.format("Error: %s\n", errorTraceDBG));
		
		ArrayList <IPredicate> interpolantsDBG = new ArrayList<IPredicate>();
		Collections.addAll(interpolantsDBG, interpolants);
		CodeCheckObserver.s_Logger.debug(String.format("Inters: %s\n", interpolantsDBG));
		
		
		
		HashMap <AnnotatedProgramPoint, ArrayList <AnnotatedProgramPoint>> nodesClones = new HashMap <AnnotatedProgramPoint, ArrayList <AnnotatedProgramPoint>>();
		// nodesClones.clear();
		
		HashMap <AnnotatedProgramPoint, HashSet <IPredicate>> map = new HashMap <AnnotatedProgramPoint, HashSet <IPredicate>>();
		
		for (int i = 0; i < interpolants.length; ++i) {
			if (!map.containsKey(nodes[i + 1])) {
				map.put(nodes[i + 1], new HashSet <IPredicate>());
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

}
