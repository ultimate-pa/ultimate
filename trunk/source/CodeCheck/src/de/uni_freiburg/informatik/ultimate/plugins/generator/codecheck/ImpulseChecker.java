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
		super(root, m_smtManager, m_truePredicate, m_falsePredicate, m_taPrefs, m_originalRoot, m_graphRoot);
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
		AnnotatedProgramPoint[] copies = new AnnotatedProgramPoint[interpolants.length];
		for(int i = 0; i < copies.length; ++i) {
			copies[i] = copyNode(nodes[i+1], interpolants[i]);
		}
		
		defaultRedirectEdges(nodes, copies);
		redirectEdges(copies);
		
		for (AnnotatedProgramPoint node : nodes)
			node.updateCopies();
		
		return true;
		
	}
	
	private AnnotatedProgramPoint copyNode(AnnotatedProgramPoint oldNode, IPredicate interpolant) {
		
		if(interpolant == m_truePredicate) {
			return oldNode;
		}
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
			newNode.connectTo(successorNode, oldNode.getOutgoingEdgeLabel(successorNode));
		}
		
		return newNode;
	}
	
	private boolean defaultRedirectEdges(AnnotatedProgramPoint[] nodes, AnnotatedProgramPoint[] copies) {
		
		//Redirect First Edge
		redirectEdge(nodes[0], nodes[1], copies[0]); 
		
		//redirect intermediate edges
		for(int i = 1; i < copies.length; ++i) {
			if(nodes[i].getNewCopies().contains(copies[i-1])) {
				if (copies[i-1].getOutgoingEdgeLabel(nodes[i+1]) instanceof Return) {
//FIXME					
				}
				else
					redirectEdge(copies[i-1], nodes[i+1], copies[i]);
			}
			else {
				AnnotatedProgramPoint source = copies[i-1];
				AnnotatedProgramPoint oldDest = findTargetInTree(source, nodes[i+1]);
				AnnotatedProgramPoint newDest = copies[i];
				
				if (oldDest == null || !isStrongerPredicate(oldDest, newDest)) {
					boolean alwaysRedirect = true;
					boolean randomlyDecide = false;
					randomlyDecide &= (Math.random() * 2) >= 1;
					if(alwaysRedirect || randomlyDecide || isStrongerPredicate(newDest, oldDest)) {
						if (source.getOutgoingEdgeLabel(oldDest) instanceof Return) {
//FIXME							
						}
						else
							redirectEdge(source, oldDest, newDest);
					}
				}
			}
		}
		
		//remove Last Edge
		AnnotatedProgramPoint lastNode = copies[copies.length - 1];
		AnnotatedProgramPoint errorLocation = nodes[nodes.length - 1];
		if (lastNode.getOutgoingNodes().contains(errorLocation)) {
			if(lastNode.getOutgoingEdgeLabel(errorLocation) instanceof Return) {
//FIXME
			}
			else
				lastNode.disconnectFrom(errorLocation);
		}
		
		return true;
	}

	private boolean redirectEdges(AnnotatedProgramPoint[] newCopies) {
		
		for (AnnotatedProgramPoint source : newCopies) {
			AnnotatedProgramPoint[] successorNodes = source.getOutgoingNodes().toArray(new AnnotatedProgramPoint[]{});
			for (AnnotatedProgramPoint oldDest : successorNodes) {
				if(source.getOutgoingEdgeLabel(oldDest) instanceof Return) {
					AnnotatedProgramPoint[] callPreds;
					callPreds = source.getCallPredsOfOutgoingReturnTarget(oldDest).toArray(new AnnotatedProgramPoint[]{});
					if(callPreds != null) {
						for (AnnotatedProgramPoint callPred : callPreds) {
							AnnotatedProgramPoint newDest = redirectionTargetFinder.findReturnRedirectionTarget(source, callPred, oldDest);
							if (newDest != null)
								redirectHyperEdgeDestination(source, callPred, oldDest, newDest);
						}
					}
				}
				else {
					AnnotatedProgramPoint newDest = redirectionTargetFinder.findRedirectionTarget(source, oldDest);
					if(newDest != null)
						redirectEdge(source, oldDest, newDest);
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
		
		if(label instanceof Return) { 
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