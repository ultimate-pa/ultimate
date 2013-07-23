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



/**
 * The implementation of Impulse ModelChecker. Given an infeasible error trace, the class refines the program graph accordingly.
 *
 * @author Mohamed Sherif
 */
public class ImpulseChecker extends CodeChecker {

	private HashMap <ProgramPoint, HashMap<IPredicate, AnnotatedProgramPoint>> LocationPredicates;
	private RedirectionTargetFinder redirectionTargetFinder;

	/**
	 * Constructor of the Impulse Checker.
	 * @param root root node of the RCFG graph
	 * @param m_smtManager the SMT Manager
	 * @param m_truePredicate the predicate true
	 * @param m_falsePredicate the predicate false
	 * @param m_taPrefs TAPreferences
	 * @param m_originalRoot the original RootNode
	 * @param m_graphRoot the ImpRootNode
	 */
	public ImpulseChecker(IElement root, SmtManager m_smtManager, IPredicate m_truePredicate, IPredicate m_falsePredicate, TAPreferences m_taPrefs, RootNode m_originalRoot, ImpRootNode m_graphRoot) {
		super(root, m_smtManager, m_truePredicate, m_falsePredicate, m_taPrefs, m_originalRoot, m_graphRoot);
		redirectionTargetFinder = new RedirectionTargetFinder(this);
		LocationPredicates = new HashMap<ProgramPoint, HashMap<IPredicate,AnnotatedProgramPoint>>();
		initializeLocationPredicates(m_graphRoot);
	}

	/**
	 * Initializes the Location-Predicates map.
	 * The location-Preicates map is a data structure maping each program point to the set of Annotated Program Points with their predicates.
	 * It's used to make sure that no 2 Annotated Program Points would have the same program point and the same annotation.
	 * The map is initialized through a Depth First Search approach.
	 * @param node the node to be explored in the dfs approach
	 * @return always returns true
	 */
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
	
	/**
	 * The primary method in the class, takes the infeasible error trace and interpolants and updates the graph accordingly.
	 * First it copies the nodes of the trace with the new annotations according to the interpolants.
	 * The new nodes contains all outgoing edges of the copied node.
	 * These outgoing nodes is then redirected.
	 * First the default redirection that do not need validity checks as the validity is guaranteed according to the Algorithm.
	 * Then the other outgoing edges are redirected to the strongest of the new copies if valid.
	 * The strongest redirection target is determined according to the redirection target finding strategy
	 * @see #copyNode(AnnotatedProgramPoint, IPredicate)
	 * @see #defaultRedirectEdges(AnnotatedProgramPoint[],AnnotatedProgramPoint[])
	 * @see #redirectEdges(AnnotatedProgramPoint[])
	 * @param nodes the infeasible error trace represented as an array of nodes
	 * @param interpolants the list of interpolants attached to the nodes of the infeasible error trace
	 * @param procedureRoot the procedure root, not needed, exists only because of inheritance
	 * @return always returns true
	 */
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
	
	/**
	 * Given an old node and an interpolant, this method returns a copy of the node.
	 * The new copy will have all outgoing edges and hyper edges of the copied node.
	 * If the new node is a duplicate of an existing node, the existing node will be returned.
	 * @see #LocationPredicates
	 * @see AnnotatedProgramPoint#AnnotatedProgramPoint(IPredicate, ProgramPoint, Boolean)
	 * @param oldNode the node that should be copied
	 * @param interpolant the interpolant that the new copy should be refined with
	 * @return returns the new copy, or an existing similar one
	 */
	private AnnotatedProgramPoint copyNode(AnnotatedProgramPoint oldNode, IPredicate interpolant) {
		// First we search for an old node similar to the one to be created, and return it if found.
		if(interpolant == m_truePredicate) {
			return oldNode;
		}
		ProgramPoint programPoint = oldNode.getProgramPoint();
		IPredicate newPredicate = conjugatePredicates(oldNode.getPredicate(), interpolant);
		AnnotatedProgramPoint newNode = LocationPredicates.get(programPoint).get(newPredicate);
		if(newNode != null)
			return newNode;
		
		// If no old node is found, a new one is created using the constructor which copies outgoing edges
		newNode = new AnnotatedProgramPoint(oldNode, newPredicate, true);
		oldNode.addCopy(newNode);
		newNode.setCloneSource(oldNode);

		// We update the LocationPredicate map with the new node, to make sure that no duplicate will be created after that.
		LocationPredicates.get(programPoint).put(newPredicate, newNode);
		
		return newNode;
	}
	
	/**
	 * Performs the default redirecting between the error trace and the new nodes.
	 * an edge between copy(node i) and node i+1 will be redirected to copy(node i+1)
	 * Also checks if the source of an edge is not a new copy but rather a similar old node, 
	 * the edge then is found and redirected
	 * @see #findTargetInTree(AnnotatedProgramPoint, AnnotatedProgramPoint)
	 * @param nodes the error trace
	 * @param copies the copies along the error trace
	 * @return always returns true
	 */
	private boolean defaultRedirectEdges(AnnotatedProgramPoint[] nodes, AnnotatedProgramPoint[] copies) {
		
		//Redirect First Edge
		redirectEdge(nodes[0], nodes[1], copies[0]); 
		
		//redirect intermediate edges
		for(int i = 1; i < copies.length; ++i) {
			if(nodes[i].getNewCopies().contains(copies[i-1])) {
				// if the source node is a new copy, then we redirect right away.
				if (copies[i-1].getOutgoingEdgeLabel(nodes[i+1]) instanceof Return) {
					// if the edge is a hyper edge, then we need to find the call pred.
//FIXME					
				}
				else
					redirectEdge(copies[i-1], nodes[i+1], copies[i]);
			}
			else {
				// if the source node is not a new copy, but a similar one,
				// then we find the old edge that should be redirected, and then decide whether to redirect or not.
				AnnotatedProgramPoint source = copies[i-1];
				AnnotatedProgramPoint oldDest = findTargetInTree(source, nodes[i+1]);
				AnnotatedProgramPoint newDest = copies[i];
				
				if (oldDest == null || !isStrongerPredicate(oldDest, newDest)) {
					// the edge is not redirected if the old edge is not found, 
					// or if the found edge destination is stronger than the new one.
					// the edge is redirected if the new destination is stronger than the old one.
					// otherwise, we either decide randomly, or decide to redirect always, or not to redirect at all.

					boolean alwaysRedirect = true;
					boolean randomlyDecide = false;
					randomlyDecide &= (Math.random() * 2) >= 1;
					if(alwaysRedirect || randomlyDecide || isStrongerPredicate(newDest, oldDest)) {
						if (source.getOutgoingEdgeLabel(oldDest) instanceof Return) {
							// if the edge is a hyper edge, then we need to find the call pred.
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

	/**
	 * Redirects the outgoing edges of new copies from old nodes to one of their copies, in case a valid target is found.
	 * @param newCopies the copies along the error trace
	 * @return always returns true
	 */
	private boolean redirectEdges(AnnotatedProgramPoint[] newCopies) {

		for (AnnotatedProgramPoint source : newCopies) {
			AnnotatedProgramPoint[] successorNodes = source.getOutgoingNodes().toArray(new AnnotatedProgramPoint[]{});
			for (AnnotatedProgramPoint oldDest : successorNodes) {
				// For each new copy, and for each of it's outgoing nodes, we search for a better redirection target
				if(source.getOutgoingEdgeLabel(oldDest) instanceof Return) {
					// If the edge is a return edge, then each hyper edge is checked for redirection
					AnnotatedProgramPoint[] callPreds;
					callPreds = source.getCallPredsOfOutgoingReturnTarget(oldDest).toArray(new AnnotatedProgramPoint[]{});
					if(callPreds != null) {
						for (AnnotatedProgramPoint callPred : callPreds) {
							// we use the target finder to find us the best redirection target. 
							// if it returns null, then no better target is found and we don't redirect.
							AnnotatedProgramPoint newDest = redirectionTargetFinder.findReturnRedirectionTarget(source, callPred, oldDest);
							if (newDest != null)
								redirectHyperEdgeDestination(source, callPred, oldDest, newDest);
						}
					}
				}
				else {
					// For normal edges, we use the target finder to find us the redirection target, and redirect.
					AnnotatedProgramPoint newDest = redirectionTargetFinder.findRedirectionTarget(source, oldDest);
					if(newDest != null)
						redirectEdge(source, oldDest, newDest);
				}
			}
		}
		return true;
	}
	
	/**
	 * Redirects an edge from it's old destination to another destination.
	 * If the edge is a return edge, then we redirect all its hyper edges.
	 * @param source the source of the edge
	 * @param oldDest the old destination of the edge
	 * @param newDest the new destination the edge will be redirected to
	 * @return returns false if there is no edge to be redirected, otherwise true
	 */
	private boolean redirectEdge(AnnotatedProgramPoint source,
			AnnotatedProgramPoint oldDest,
			AnnotatedProgramPoint newDest) {
		
		CodeBlock label = source.getOutgoingEdgeLabel(oldDest);
		if(label == null)
			return false;

		source.connectTo(newDest, label);
		
		// Usually I make sure not to use this method if it's a return edge. But I wrote this part anyway for future uses maybe
		if(label instanceof Return) { 
			 HashSet<AnnotatedProgramPoint> callPreds = source.getCallPredsOfOutgoingReturnTarget(oldDest);
			 for(AnnotatedProgramPoint callPred : callPreds)
				 source.addOutGoingReturnCallPred(newDest, callPred);
		}
		
		source.disconnectFrom(oldDest);
		
		return true;
		
	}
	
	/**
	 * Redirects a hyper edge from it's old destination to another destination.
	 * @param source the source of the hyper edge
	 * @param callPred the call predecessor of the hyper edge
	 * @param oldDest the old destination of the hyper edge
	 * @param newDest the new destination the hyper edge will be redirected to
	 * @return returns false if there is no hyper edge to be redirected, otherwise true
	 */
	private boolean redirectHyperEdgeDestination(AnnotatedProgramPoint source, AnnotatedProgramPoint callPred,
			AnnotatedProgramPoint oldDest,
			AnnotatedProgramPoint newDest) {
		
		CodeBlock label = source.getOutgoingEdgeLabel(oldDest);
		if(label == null || !(label instanceof Return))
			return false;

		// We add the label of the hyper edge via the connectTo method.
		// If the already exists, the connectTo method will detect that and create no duplicates
		source.connectTo(newDest, label);

		source.addOutGoingReturnCallPred(newDest, callPred);
		source.removeOutgoingReturnCallPred(oldDest, callPred);

		// If that was the last hyper edge connecting the source and old destination, then the 2 are disconnected.
		if(source.getCallPredsOfOutgoingReturnTarget(oldDest) == null)
			source.disconnectFrom(oldDest);
		
		return true;
		
	}
	
	/**
	 * Search for an edge between the source and the root or one of its children.
	 * @param source the source of the edge
	 * @param root the root of the tree where the search starts
	 * @return returns the destination of the found edge, returns null if no edge is found
	 */
	private AnnotatedProgramPoint findTargetInTree(AnnotatedProgramPoint source, AnnotatedProgramPoint root) {
		// If the source is connected to the root, then we return the root,
		// otherwise we search in its children in a dfs approach.
		// It's a tree, no cycles, so we don't need a list for visited nodes.
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