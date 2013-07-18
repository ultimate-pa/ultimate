package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;



public class ImpulseChecker extends CodeChecker {

	private HashMap <ProgramPoint, HashMap<IPredicate, AnnotatedProgramPoint>> LocationPredicates;
	private RedirectionTargetFinder redirectionTargetFinder;

	public ImpulseChecker(IElement root, SmtManager m_smtManager, IPredicate m_truePredicate, IPredicate m_falsePredicate, TAPreferences m_taPrefs, RootNode m_originalRoot, ImpRootNode m_graphRoot) {
		super(root, m_smtManager, m_falsePredicate, m_falsePredicate, m_taPrefs, m_originalRoot, m_graphRoot);
		redirectionTargetFinder = new RedirectionTargetFinder(this);
		LocationPredicates = new HashMap<ProgramPoint, HashMap<IPredicate,AnnotatedProgramPoint>>();
		initializeLocationPredicates(m_graphRoot);
	}

	private boolean initializeLocationPredicates(AnnotatedProgramPoint node) {
		ProgramPoint programPoint = node.getProgramPoint();
		if(LocationPredicates.get(programPoint) == null) {
			HashMap<IPredicate,AnnotatedProgramPoint> hashMap = new HashMap<IPredicate,AnnotatedProgramPoint>();
			hashMap.put(node.getPredicate(), node);
			LocationPredicates.put(programPoint, hashMap);
			for (AnnotatedProgramPoint successor : node.getOutgoingNodes())
				initializeLocationPredicates(successor);
		}
		return true;
	}
	
	public boolean codeCheck(AnnotatedProgramPoint[] nodes, IPredicate[] interpolants, AnnotatedProgramPoint procedureRoot) {
		
		AnnotatedProgramPoint[] copies = new AnnotatedProgramPoint[interpolants.length + 1];
		for(int i = 1; i < copies.length; ++i) {
			copies[i] = copyNode(nodes[i], interpolants[i-1]);
		}
		
		defaultRedirectEdges(nodes, copies);
		redirectEdges(nodes);
		
		for (AnnotatedProgramPoint node : nodes)
			node.updateCopies();
		
		return true;
		
	}
	
	private AnnotatedProgramPoint copyNode(AnnotatedProgramPoint oldNode, IPredicate interpolant) {
		if(interpolant == m_truePredicate) // Alex :
			return oldNode;
		ProgramPoint programPoint = oldNode.getProgramPoint();
		IPredicate newPredicate = conjugatePredicates(oldNode.getPredicate(), interpolant);
		AnnotatedProgramPoint newNode = LocationPredicates.get(programPoint).get(newPredicate);
		if(newNode != null)
			return newNode;

		newNode = new AnnotatedProgramPoint(oldNode, newPredicate, true);
		LocationPredicates.get(programPoint).put(newPredicate, newNode);
		oldNode.addCopy(newNode);
		newNode.setCloneSource(oldNode);

		AnnotatedProgramPoint[] successorNodes = oldNode.getOutgoingNodes().toArray(new AnnotatedProgramPoint[]{});
		for (AnnotatedProgramPoint successorNode : successorNodes) {
			CodeBlock label = oldNode.getOutgoingEdgeLabel(successorNode);
			newNode.addOutgoingNode(successorNode, label);
			successorNode.addIncomingNode(newNode);
		}
		
		return newNode;
	}
	
	private boolean defaultRedirectEdges(AnnotatedProgramPoint[] nodes, AnnotatedProgramPoint[] copies) {
		
		//Redirect First Edge
		redirectEdge(nodes[0], nodes[1], copies[1]); 
		
		//redirect intermediate edges
		for(int i = 1; i < copies.length - 1; ++i) {

			
			if(nodes[i].getNewCopies().contains(copies[i]))
				redirectEdge(copies[i], nodes[i+1], copies[i+1]);
			else {
				AnnotatedProgramPoint source = copies[i];
				AnnotatedProgramPoint oldDest = findTargetInTree(source, nodes[i+1]);
				AnnotatedProgramPoint newDest = copies[i+1];
				
				if (oldDest != null && !isStrongerPredicate(oldDest, newDest)) {
					boolean alwaysRedirect = false;
					boolean randomlyDecide = false;
					randomlyDecide &= (Math.random() * 2) >= 1;
					if(alwaysRedirect || randomlyDecide || isStrongerPredicate(newDest, oldDest))
						redirectEdge(source, oldDest, newDest);
				}
			}
		}
		
		//remove Last Edge
		AnnotatedProgramPoint lastNode = copies[copies.length - 1];
		AnnotatedProgramPoint errorLocation = nodes[nodes.length - 1];
		if (lastNode.getOutgoingNodes().contains(errorLocation)) {
			lastNode.disconnectFrom(errorLocation);
		}
		
		return true;
	}

	private boolean redirectEdges(AnnotatedProgramPoint[] nodes) {
		
		for (AnnotatedProgramPoint node : nodes) {
			AnnotatedProgramPoint[] predecessorNodes = node.getIncomingNodes().toArray(new AnnotatedProgramPoint[]{});
			for (AnnotatedProgramPoint predecessorNode : predecessorNodes) {
				if(predecessorNode != m_graphRoot) {
					if(predecessorNode.getOutgoingEdgeLabel(node) instanceof Return) {
						HashSet<AnnotatedProgramPoint> callPreds;
						callPreds = predecessorNode.getCallPredsOfOutgoingReturnTarget(node);
						if(callPreds != null) {
							for (AnnotatedProgramPoint callPred : callPreds) {
								AnnotatedProgramPoint newDest = redirectionTargetFinder.findReturnRedirectionTarget(predecessorNode, callPred, node);
								if (newDest != null)
									redirectHyperEdgeDestination(predecessorNode, callPred, node, newDest);
							}
						}
					}
					else {
						AnnotatedProgramPoint newDest = redirectionTargetFinder.findRedirectionTarget(predecessorNode, node);
						if(newDest != null)
							redirectEdge(predecessorNode, node, newDest);
					}
				}
			}
			
			HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>> hyperEdgesToCallPred;
			hyperEdgesToCallPred = node.m_ingoingReturnAppToCallPreds;
			AnnotatedProgramPoint[] sources = hyperEdgesToCallPred.keySet().toArray(new AnnotatedProgramPoint[]{});
			for (AnnotatedProgramPoint source : sources) {
				AnnotatedProgramPoint[] targets = hyperEdgesToCallPred.get(source).toArray(new AnnotatedProgramPoint[]{});
				for (AnnotatedProgramPoint target : targets) {
					AnnotatedProgramPoint newCallPred = redirectionTargetFinder.findReturnRedirectionCallPred(node, source, target);
					if(newCallPred != null)
						redirectHyperEdgeCallPred(source, node, newCallPred, target);
				}
			}
		}
		return true;
	}
	
	private boolean redirectEdge(AnnotatedProgramPoint source,
			AnnotatedProgramPoint oldDest,
			AnnotatedProgramPoint newDest) {
		
		CodeBlock label = source.getOutgoingEdgeLabel(oldDest);
		if(label == null)
			return false;
		source.connectTo(newDest, label);
		if(label instanceof Return) { //FIXME how to default redirect return edges?
			 HashSet<AnnotatedProgramPoint> callPreds = source.getCallPredsOfOutgoingReturnTarget(oldDest);
			 for(AnnotatedProgramPoint callPred : callPreds)
				 source.addOutGoingReturnCallPred(newDest, callPred);
		}
		source.disconnectFrom(oldDest);
		
		return true;
		
	}
	
	private boolean redirectHyperEdgeDestination(AnnotatedProgramPoint source, AnnotatedProgramPoint callPred,
			AnnotatedProgramPoint oldDest,
			AnnotatedProgramPoint newDest) {
		
		CodeBlock label = source.getOutgoingEdgeLabel(oldDest);
		if(label == null || !(label instanceof Return))
			return false;
		source.connectTo(newDest, label);
		source.addOutGoingReturnCallPred(newDest, callPred);
		source.removeOutgoingReturnCallPred(oldDest, callPred);
		if(source.getCallPredsOfOutgoingReturnTarget(oldDest) == null)
			source.disconnectFrom(oldDest);
		
		return true;
		
	}
	
	private boolean redirectHyperEdgeCallPred(AnnotatedProgramPoint source, AnnotatedProgramPoint oldCallPred,
			AnnotatedProgramPoint newCallPred,
			AnnotatedProgramPoint dest) {
		
		CodeBlock label = source.getOutgoingEdgeLabel(dest);
		if(label == null || !(label instanceof Return))
			return false;
		source.addOutGoingReturnCallPred(dest, newCallPred);
		source.removeOutgoingReturnCallPred(dest, oldCallPred);
		
		return true;
		
	}
	
	private AnnotatedProgramPoint findTargetInTree(AnnotatedProgramPoint source, AnnotatedProgramPoint root) {
		if(source.getOutgoingNodes().contains(root))
			return root;
		for(AnnotatedProgramPoint child : root.getCopies()) {
			AnnotatedProgramPoint res = findTargetInTree(source, child);
			if(res != null)
				return res;
		}
		return null;
	}
	
	
	
}
