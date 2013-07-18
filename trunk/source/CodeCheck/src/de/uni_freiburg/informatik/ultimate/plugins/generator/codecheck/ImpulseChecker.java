package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;


enum RedirectionMethod {
	First, FirstStrongest, Random, RandomStrongest, Alex
}

public class ImpulseChecker extends CodeChecker {

	private HashMap <ProgramPoint, HashMap<IPredicate, AnnotatedProgramPoint>> LocationPredicates;
	private static RedirectionMethod redirectionMethod;

	public ImpulseChecker(IElement root, SmtManager m_smtManager, IPredicate m_truePredicate, IPredicate m_falsePredicate, TAPreferences m_taPrefs, RootNode m_originalRoot, ImpRootNode m_graphRoot) {
		super(root, m_smtManager, m_falsePredicate, m_falsePredicate, m_taPrefs, m_originalRoot, m_graphRoot);
		redirectionMethod = RedirectionMethod.RandomStrongest; // Alex : Change that variable here

		LocationPredicates = new HashMap<ProgramPoint, HashMap<IPredicate,AnnotatedProgramPoint>>();
		initializeLocationPredicates(m_graphRoot);
	}
	private boolean updateSets(AnnotatedProgramPoint oldNode) {
		// This is assuming that a copy of a node will never be an original node.
		for (HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>> map : hashMaps) {
			if (map.containsKey(oldNode)) {
				HashSet <AnnotatedProgramPoint> hyperEdges = map.get(oldNode);
				//map.remove(oldNode);
				for (Iterator <AnnotatedProgramPoint> clones = oldNode.getNewCopies().iterator(); clones.hasNext(); ) {
					AnnotatedProgramPoint newNode = clones.next();
					map.put(newNode, hyperEdges);
				}
			}
		}
		
		for (HashSet<AnnotatedProgramPoint> set : hashSets) {
			if (set.contains(oldNode)) {
				for (Iterator <AnnotatedProgramPoint> clones = oldNode.getNewCopies().iterator(); clones.hasNext(); ) {
					AnnotatedProgramPoint newNode = clones.next();
					set.add(newNode);
				}
			}
		}
		return true;
	}
	
	private boolean isStrongerPredicate(AnnotatedProgramPoint strongerNode, AnnotatedProgramPoint weakerNode, CodeBlock dummyLabel) {
		
		if (dummyLabel == null)
			dummyLabel = new DummyCodeBlock();
		
		if (isValidEdge(weakerNode, dummyLabel, strongerNode))
			return true;
		else
			return false;
		
	}
	
	public boolean codeCheck(AnnotatedProgramPoint[] nodes, IPredicate[] interpolants, AnnotatedProgramPoint procedureRoot) {
		
		AnnotatedProgramPoint[] copies = new AnnotatedProgramPoint[interpolants.length + 1];
		for(int i = 1; i < copies.length; ++i) {
			copies[i] = copyNode(nodes[i], interpolants[i-1]);
		}
		
		redirectEdges(nodes, copies);
		
		for (AnnotatedProgramPoint node : nodes) {
			updateSets(node); 
			node.updateCopies();
		}
		
		return true;
		
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
	
	private AnnotatedProgramPoint copyNode(AnnotatedProgramPoint oldNode, IPredicate interpolant) {
		
		
		if(interpolant == m_truePredicate) // Alex :
			return oldNode;
		
		
		ProgramPoint programPoint = oldNode.getProgramPoint();
		
		IPredicate newPredicate = conjugatePredicates(oldNode.getPredicate(), interpolant);

		AnnotatedProgramPoint newNode = LocationPredicates.get(programPoint).get(newPredicate);
		
		if(newNode != null)
			return newNode;
		
		newNode = new AnnotatedProgramPoint(oldNode, newPredicate);
		
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

	private boolean redirectEdges(AnnotatedProgramPoint[] nodes, AnnotatedProgramPoint[] copies) {
		
		defaultRedirecting(nodes, copies);
		
		for (AnnotatedProgramPoint node : nodes) {
			
			AnnotatedProgramPoint[] predecessorNodes = node.getIncomingNodes().toArray(new AnnotatedProgramPoint[]{});
			
			for (AnnotatedProgramPoint predecessorNode : predecessorNodes) {
				
				if(predecessorNode == m_graphRoot) 
					continue;
				
				AnnotatedProgramPoint bestRedirectTarget = findBestRedirectionTarget(predecessorNode, node);
				
				if(bestRedirectTarget != null)
					redirect(predecessorNode, node, bestRedirectTarget);
			}
		}
	
		return true;
	}
	
	private boolean defaultRedirecting(AnnotatedProgramPoint[] nodes, AnnotatedProgramPoint[] copies) {
		
		CodeBlock dummyCodeBlock = new DummyCodeBlock();
		
		//Redirect First Edge
		redirect(nodes[0], nodes[1], copies[1]); 
		
		//redirect intermediate edges
		for(int i = 1; i < copies.length - 1; ++i) {

			
			if(nodes[i].getNewCopies().contains(copies[i]))
				redirect(copies[i], nodes[i+1], copies[i+1]);
			else {
				AnnotatedProgramPoint source = copies[i];
				AnnotatedProgramPoint oldDest = null; //FIXME
				AnnotatedProgramPoint newDest = copies[i+1];
				
				
				if (oldDest == null) 
					; //ask alex
				else if (isStrongerPredicate(newDest, oldDest, dummyCodeBlock))
					redirect(source, oldDest, newDest);
				else if (isStrongerPredicate(oldDest, newDest, dummyCodeBlock))
					; //do nothing
				else {
					boolean alwaysRedirect = false;
					boolean randomlyDecide = false;
					
					if(alwaysRedirect)
						redirect(source, oldDest, newDest);
					else if(randomlyDecide) {
						int rand = (int)(Math.random() * 2);
						if(rand == 1)
							redirect(source, oldDest, newDest);
					}
				}
			}
		}
		
		//remove Last Edge
		AnnotatedProgramPoint lastNode = copies[copies.length - 1];
		AnnotatedProgramPoint errorLocation = nodes[nodes.length-1];
		if (lastNode.getOutgoingNodes().contains(errorLocation)) { //FIXME
			lastNode.removeOutgoingNode(errorLocation);
			errorLocation.removeIncomingNode(lastNode);
		}
		
		return true;
	}
	
	private boolean redirect(AnnotatedProgramPoint source,
			AnnotatedProgramPoint oldDest,
			AnnotatedProgramPoint newDest) {
		
		CodeBlock label = source.getOutgoingEdgeLabel(oldDest);
		if(label == null)
			return false;
		source.removeOutgoingNode(oldDest);
		oldDest.removeIncomingNode(source);
		source.addOutgoingNode(newDest, label);
		newDest.addIncomingNode(source);
		
		return true;
		
	}

	private AnnotatedProgramPoint findBestRedirectionTarget(
			AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint node) {
		switch(redirectionMethod) {
		case First: return findFirstRedirectionTarget(predecessorNode, node);
		case FirstStrongest: return findFirstStrongestRedirectionTarget(predecessorNode, node);
		case Random: return findRandomRedirectionTarget(predecessorNode, node);
		case RandomStrongest: return findRandomStrongestRedirectionTarget(predecessorNode, node);
		case Alex: return null; //FIXME // Alex : Write your redirection algorithm here.
		default: return null;
		}
		//return result;
	}
	
	private AnnotatedProgramPoint findFirstRedirectionTarget(AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint node) {

		CodeBlock label = predecessorNode.getOutgoingEdgeLabel(node);
		
		ArrayList <AnnotatedProgramPoint> candidates = node.getNewCopies();
		
		for (AnnotatedProgramPoint candidate : candidates) {
			if(isValidEdge(predecessorNode, label, candidate)) {
				return candidate;
			}
		}
		
		return null;
		
	}
	
	private AnnotatedProgramPoint findFirstStrongestRedirectionTarget(AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint node) {

		CodeBlock label = predecessorNode.getOutgoingEdgeLabel(node);
		
		ArrayList <AnnotatedProgramPoint> candidates = node.getNewCopies();
		
		AnnotatedProgramPoint target = null;
		
		CodeBlock dummyLabel = new DummyCodeBlock();
		
		for (AnnotatedProgramPoint candidate : candidates) {
			if(isValidEdge(predecessorNode, label, candidate)) {
				if(target == null || isStrongerPredicate(candidate, target, dummyLabel))
					target = candidate;
			}
		}
		
		return target;
		
	}
	
	private AnnotatedProgramPoint findRandomRedirectionTarget(AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint node) {

		CodeBlock label = predecessorNode.getOutgoingEdgeLabel(node);
		
		ArrayList <AnnotatedProgramPoint> candidates = node.getNewCopies();
		
		Collections.shuffle(candidates);
		
		for (AnnotatedProgramPoint candidate : candidates) {
			if(isValidEdge(predecessorNode, label, candidate)) {
				return candidate;
			}
		}
		
		return null;
		
	}
	
	private AnnotatedProgramPoint findRandomStrongestRedirectionTarget(AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint node) {

		CodeBlock label = predecessorNode.getOutgoingEdgeLabel(node);
		
		ArrayList <AnnotatedProgramPoint> candidates = node.getNewCopies();
		
		Collections.shuffle(candidates);
		
		AnnotatedProgramPoint target = null;
		
		CodeBlock dummyLabel = new DummyCodeBlock();
		
		for (AnnotatedProgramPoint candidate : candidates) {
			if(isValidEdge(predecessorNode, label, candidate)) {
				if(target == null || isStrongerPredicate(candidate, target, dummyLabel))
					target = candidate;
			}
		}
		
		return target;
		
	}
}
