package de.uni_freiburg.informatik.ultimate.plugins.generator.impulse;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AnnotatedProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppHyperEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.ImpRootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.CodeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.GraphWriter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * The implementation of Impulse ModelChecker. Given an infeasible error trace,
 * the class refines the program graph accordingly.
 * 
 * @author Mohamed Sherif
 */
public class ImpulseChecker extends CodeChecker {

	private HashMap<ProgramPoint, HashMap<IPredicate, AnnotatedProgramPoint>> LocationPredicates;
	private RedirectionTargetFinder redirectionTargetFinder;

	/**
	 * Constructor of the Impulse Checker.
	 * 
	 * @param root
	 *            root node of the RCFG graph
	 * @param m_smtManager
	 *            the SMT Manager
	 * @param m_truePredicate
	 *            the predicate true
	 * @param m_falsePredicate
	 *            the predicate false
	 * @param m_taPrefs
	 *            TAPreferences
	 * @param m_originalRoot
	 *            the original RootNode
	 * @param m_graphRoot
	 *            the ImpRootNode
	 * @param logger
	 * @param m_predicateUnifier
	 * @param m_edgeChecker
	 * @param m_graphWriter
	 */
	public ImpulseChecker(IElement root, SmtManager m_smtManager, IPredicate m_truePredicate,
			IPredicate m_falsePredicate, TAPreferences m_taPrefs, RootNode m_originalRoot, ImpRootNode m_graphRoot,
			GraphWriter graphWriter, EdgeChecker edgeChecker, PredicateUnifier predicateUnifier, Logger logger) {
		super(root, m_smtManager, m_truePredicate, m_falsePredicate, m_taPrefs, m_originalRoot, m_graphRoot,
				graphWriter, edgeChecker, predicateUnifier, logger);
		redirectionTargetFinder = new RedirectionTargetFinder(this);
		LocationPredicates = new HashMap<ProgramPoint, HashMap<IPredicate, AnnotatedProgramPoint>>();
		initializeLocationPredicates(m_graphRoot);
	}

	/**
	 * Initializes the Location-Predicates map. The location-Preicates map is a
	 * data structure maping each program point to the set of Annotated Program
	 * Points with their predicates. It's used to make sure that no 2 Annotated
	 * Program Points would have the same program point and the same annotation.
	 * The map is initialized through a Depth First Search approach.
	 * 
	 * @param node
	 *            the node to be explored in the dfs approach
	 * @return always returns true
	 */
	private boolean initializeLocationPredicates(AnnotatedProgramPoint node) {
		ProgramPoint programPoint = node.getProgramPoint();
		if (LocationPredicates.get(programPoint) == null) {
			HashMap<IPredicate, AnnotatedProgramPoint> hashMap = new HashMap<IPredicate, AnnotatedProgramPoint>();
			hashMap.put(node.getPredicate(), node);
			LocationPredicates.put(programPoint, hashMap);
			for (AnnotatedProgramPoint successor : node.getOutgoingNodes())
				initializeLocationPredicates(successor);
		}
		return true;
	}

	/**
	 * The primary method in the class, takes the infeasible error trace and
	 * interpolants and updates the graph accordingly. First it copies the nodes
	 * of the trace with the new annotations according to the interpolants. The
	 * new nodes contains all outgoing edges of the copied node. These outgoing
	 * nodes is then redirected. First the default redirection that do not need
	 * validity checks as the validity is guaranteed according to the Algorithm.
	 * Then the other outgoing edges are redirected to the strongest of the new
	 * copies if valid. The strongest redirection target is determined according
	 * to the redirection target finding strategy
	 * 
	 * @see #copyNode(AnnotatedProgramPoint, IPredicate)
	 * @see #defaultRedirectEdges(AnnotatedProgramPoint[],AnnotatedProgramPoint[])
	 * @see #redirectEdges(AnnotatedProgramPoint[])
	 * @param errorRun
	 *            the infeasible error trace found by the emptiness check
	 * @param interpolants
	 *            the list of interpolants attached to the nodes of the
	 *            infeasible error trace
	 * @param procedureRoot
	 *            the procedure root, not needed, exists only because of
	 *            inheritance
	 * @return always returns true
	 */
	public boolean codeCheck(NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun, IPredicate[] interpolants,
			AnnotatedProgramPoint procedureRoot) {
		AnnotatedProgramPoint[] nodes = errorRun.getStateSequence().toArray(new AnnotatedProgramPoint[0]);
		// Debugging
		// debug1(interpolants, nodes);

		// Debugging
		// debug2(nodes, errorRun.getWord());

		AnnotatedProgramPoint[] copies = new AnnotatedProgramPoint[interpolants.length];
		for (int i = 0; i < copies.length; ++i) {
			copies[i] = copyNode(nodes[i + 1], interpolants[i]);
		}

		defaultRedirectEdges(nodes, errorRun, copies);
		redirectEdges(copies, errorRun);

		for (AnnotatedProgramPoint node : nodes)
			node.updateCopies();

		return true;

	}

	@Override
	public boolean codeCheck(NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun, IPredicate[] interpolants,
			AnnotatedProgramPoint procedureRoot,
			HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>> _satTriples,
			HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>> _unsatTriples) {
		// TODO Auto-generated method stub --> make use of memoization maps
		return this.codeCheck(errorRun, interpolants, procedureRoot);
	}

	@Override
	public boolean codeCheck(NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun, IPredicate[] interpolants,
			AnnotatedProgramPoint procedureRoot,
			HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>> _satTriples,
			HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>> _unsatTriples,
			HashMap<IPredicate, HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>>> _satQuadruples,
			HashMap<IPredicate, HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>>> _unsatQuadruples) {
		// TODO Auto-generated method stub
		return false;
	}

	/**
	 * Given an old node and an interpolant, this method returns a copy of the
	 * node. The new copy will have all outgoing edges and hyper edges of the
	 * copied node. If the new node is a duplicate of an existing node, the
	 * existing node will be returned.
	 * 
	 * @see #LocationPredicates
	 * @see AnnotatedProgramPoint#AnnotatedProgramPoint(IPredicate,
	 *      ProgramPoint, Boolean)
	 * @param oldNode
	 *            the node that should be copied
	 * @param interpolant
	 *            the interpolant that the new copy should be refined with
	 * @return returns the new copy, or an existing similar one
	 */
	private AnnotatedProgramPoint copyNode(AnnotatedProgramPoint oldNode, IPredicate interpolant) {
		// First we search for an old node similar to the one to be created, and
		// return it if found.
		if (interpolant == m_truePredicate) {
			return oldNode;
		}
		ProgramPoint programPoint = oldNode.getProgramPoint();
		IPredicate newPredicate = conjugatePredicates(oldNode.getPredicate(), interpolant);
		AnnotatedProgramPoint newNode = LocationPredicates.get(programPoint).get(newPredicate);
		if (newNode != null)
			return newNode;

		// If no old node is found, a new one is created using the constructor
		// which copies outgoing edges
		newNode = new AnnotatedProgramPoint(oldNode, newPredicate, true);
		oldNode.addCopy(newNode);
		newNode.setCloneSource(oldNode);

		// We update the LocationPredicate map with the new node, to make sure
		// that no duplicate will be created after that.
		LocationPredicates.get(programPoint).put(newPredicate, newNode);

		return newNode;
	}

	/**
	 * Performs the default redirecting between the error trace and the new
	 * nodes. an edge between copy(node i) and node i+1 will be redirected to
	 * copy(node i+1) Also checks if the source of an edge is not a new copy but
	 * rather a similar old node, the edge then is found and redirected
	 * 
	 * @see #findTargetInTree(AnnotatedProgramPoint, AnnotatedProgramPoint)
	 * @param nodes
	 *            the nodes of the error trace
	 * @param errorRun
	 *            the nested word of the error trace, used to get call
	 *            predecessors of return edges
	 * @param copies
	 *            the copies along the error trace
	 * @return always returns true
	 */
	private boolean defaultRedirectEdges(AnnotatedProgramPoint[] nodes,
			NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun, AnnotatedProgramPoint[] copies) {
		// TODO: f�r Impulse braucht man wohl den error run im sinne von
		// AppEdges -- zumindst f�r das default redirecting
		// kann man rekonstruieren aus den beiden angrenzenden Knoten, dem label
		// aus dem errorRun und ggf der NestingRelation
		// --> lohnt sich's?

		AppEdge firstEdge = reconstructWhichEdge(nodes[0], nodes[1], errorRun.getSymbol(0), null);

		// Redirect First Edge
		// redirectEdge(nodes[0], nodes[1], copies[0]);
		redirectEdge(firstEdge, copies[0]);

		// redirect intermediate edges
		for (int i = 1; i < copies.length; ++i) {
			if (nodes[i].getNewCopies().contains(copies[i - 1])) {
				// if the source node is a new copy, then we redirect right
				// away.
				// if (copies[i-1].getOutgoingEdgeLabel(nodes[i+1]) instanceof
				// Return) { //--> commented out as the return case moved into
				// redirectEdge
				// // if the edge is a hyper edge, then we need to find the call
				// pred.
				// AnnotatedProgramPoint callPred =
				// nodes[nestedWord.getCallPosition(i)];
				// // System.err.printf("Removing return edge %d:%d -> %d", i,
				// nestedWords.getCallPosition(i), i+1); // for debugging
				// redirectHyperEdgeDestination(copies[i-1], callPred,
				// nodes[i+1], copies[i]);
				// }
				AppEdge edge = reconstructWhichEdge(
						copies[i - 1],
						nodes[i + 1],
						errorRun.getWord().getSymbol(i),
						errorRun.getWord().getSymbol(i) instanceof Return ? errorRun.getStateAtPosition(errorRun
								.getWord().getCallPosition(i)) : null);
				// redirectEdge(copies[i-1], nodes[i+1], copies[i]);
				redirectEdge(edge, copies[i]);
			} else {
				// if the source node is not a new copy, but a similar one,
				// then we find the old edge that should be redirected, and then
				// decide whether to redirect or not.
				AnnotatedProgramPoint source = copies[i - 1];
				AnnotatedProgramPoint oldDest = findTargetInTree(source, nodes[i + 1]);
				AnnotatedProgramPoint newDest = copies[i];

				if (oldDest != null && !isStrongerPredicate(oldDest, newDest)) {
					// the edge is not redirected if the old edge is not found,
					// or if the found edge destination is stronger than the new
					// one.
					// the edge is redirected if the new destination is stronger
					// than the old one.
					// otherwise, we either decide randomly, or decide to
					// redirect always, or not to redirect at all.

					boolean alwaysRedirect = true;
					boolean randomlyDecide = false;
					randomlyDecide &= (Math.random() * 2) >= 1;
					if (alwaysRedirect || randomlyDecide || isStrongerPredicate(newDest, oldDest)) {
						AppEdge edge = reconstructWhichEdge(
								source,
								oldDest,
								errorRun.getWord().getSymbol(i),
								errorRun.getWord().getSymbol(i) instanceof Return ? errorRun
										.getStateAtPosition(errorRun.getWord().getCallPosition(i)) : null);
						// redirectEdge(source, oldDest, newDest);
						redirectEdge(edge, newDest);
					}
				}
			}
		}

		// remove Last Edge
		AnnotatedProgramPoint lBoogieASTNode = copies[copies.length - 1];
		AnnotatedProgramPoint errorLocation = nodes[nodes.length - 1];
		if (lBoogieASTNode.getOutgoingNodes().contains(errorLocation)) {
			// if(lBoogieASTNode.getOutgoingEdgeLabel(errorLocation) instanceof
			// Return) {
			// AnnotatedProgramPoint callPred =
			// nodes[nestedWord.getCallPosition(nodes.length - 2)];
			// // System.err.printf("Removing return edge %d:%d -> %d",
			// nodes.length-2, nestedWords.getCallPosition(nodes.length-2),
			// nodes.length-1); //for debugging
			// lBoogieASTNode.removeOutgoingReturnCallPred(errorLocation,
			// callPred);
			// }
			// else
			AppEdge edge = reconstructWhichEdge(
					lBoogieASTNode,
					errorLocation,
					errorRun.getWord().getSymbol(nodes.length - 2),
					errorRun.getWord().getSymbol(nodes.length - 2) instanceof Return ? errorRun
							.getStateAtPosition(errorRun.getWord().getCallPosition(nodes.length - 2)) : null);
			// lBoogieASTNode.disconnectOutgoing(errorLocation);
			edge.disconnect();
		}

		return true;
	}

	private AppEdge reconstructWhichEdge(AnnotatedProgramPoint source, AnnotatedProgramPoint target,
			CodeBlock statement, AnnotatedProgramPoint hier) {
		for (AppEdge ae : source.getOutgoingEdges()) {
			if (ae.getTarget().equals(target) && ae.getStatement().equals(statement)) {
				if (ae instanceof AppHyperEdge) {
					AppHyperEdge ahe = (AppHyperEdge) ae;
					if (ahe.getHier().equals(hier))
						return ae;
				} else
					return ae;
			}
		}
		assert false;
		return null;
	}

	/**
	 * Redirects the outgoing edges of new copies from old nodes to one of their
	 * copies, in case a valid target is found.
	 * 
	 * @param newCopies
	 *            the copies along the error trace
	 * @param errorRun
	 * @return always returns true
	 */
	private boolean redirectEdges(AnnotatedProgramPoint[] newCopies,
			NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun) {

		// for (AnnotatedProgramPoint source : newCopies) {
		for (int i = 0; i < newCopies.length; i++) {
			AnnotatedProgramPoint source = newCopies[i];

			// AnnotatedProgramPoint[] successorNodes =
			// source.getOutgoingNodes().toArray(new AnnotatedProgramPoint[]{});
			AppEdge[] outEdges = source.getOutgoingEdges().toArray(new AppEdge[] {});
			// for (AnnotatedProgramPoint oldDest : successorNodes) {
			for (AppEdge outEdge : outEdges) {

				// AnnotatedProgramPoint newDest =
				// redirectionTargetFinder.findRedirectionTarget(source,
				// oldDest);
				AnnotatedProgramPoint newDest = redirectionTargetFinder.findRedirectionTarget(outEdge);
				if (newDest != null) {
					// AppEdge edge = reconstructWhichEdge(source, oldDest,
					// errorRun.getWord().getSymbol(i),
					// errorRun.getWord().getSymbol(i) instanceof Return ?
					// errorRun.getStateAtPosition(errorRun.getWord().getCallPosition(i))
					// :
					// null);
					redirectEdge(outEdge, newDest);
				}
				// TODO: treat return edges --> maybe just adapt the
				// redirectionTargetFinder
			}
		}
		return true;
	}

	/**
	 * Redirects an edge from it's old destination to another destination. If
	 * the edge is a return edge, then we redirect all its hyper edges.
	 * 
	 * @param source
	 *            the source of the edge
	 * @param oldDest
	 *            the old destination of the edge
	 * @param newDest
	 *            the new destination the edge will be redirected to
	 * @return returns false if there is no edge to be redirected, otherwise
	 *         true
	 */
	private boolean redirectEdge(AppEdge edge, AnnotatedProgramPoint newDest) {
		// AnnotatedProgramPoint source,
		// AnnotatedProgramPoint oldDest,
		// AnnotatedProgramPoint newDest) {
		AnnotatedProgramPoint source = edge.getSource();
		AnnotatedProgramPoint oldDest = edge.getTarget();

		if (oldDest == newDest) // IF the new Dest is the same as the old Dest,
								// then nothing needs to be done
			return true;

		CodeBlock label = edge.getStatement();
		if (label == null) {
			assert false; // does this happen? when?
			return false;
		}

		if (label instanceof Return) {
			source.connectOutgoingReturn(((AppHyperEdge) edge).getHier(), (Return) edge.getStatement(), newDest);
		} else {
			source.connectOutgoing(label, newDest);
		}

		edge.disconnect();
		return true;
	}

	/**
	 * Search for an edge between the source and the root or one of its
	 * children.
	 * 
	 * @param source
	 *            the source of the edge
	 * @param root
	 *            the root of the tree where the search starts
	 * @return returns the destination of the found edge, returns null if no
	 *         edge is found
	 */
	private AnnotatedProgramPoint findTargetInTree(AnnotatedProgramPoint source, AnnotatedProgramPoint root) {
		// If the source is connected to the root, then we return the root,
		// otherwise we search in its children in a dfs approach.
		// It's a tree, no cycles, so we don't need a list for visited nodes.
		if (source.getOutgoingNodes().contains(root))
			return root;
		for (AnnotatedProgramPoint child : root.getCopies()) {
			AnnotatedProgramPoint res = findTargetInTree(source, child);
			if (res != null)
				return res;
		}
		return null;
	}

	private void debug1(IPredicate[] interpolants, AnnotatedProgramPoint[] nodes) {
		ArrayList<AnnotatedProgramPoint> errorTraceDBG = new ArrayList<AnnotatedProgramPoint>();
		Collections.addAll(errorTraceDBG, nodes);
		mLogger.debug(String.format("Error: %s\n", errorTraceDBG));

		ArrayList<IPredicate> interpolantsDBG = new ArrayList<IPredicate>();
		Collections.addAll(interpolantsDBG, interpolants);
		mLogger.debug(String.format("Inters: %s\n", interpolantsDBG));
	}

	private void debug2(AnnotatedProgramPoint[] nodes, NestedWord<CodeBlock> nestedWords) {
		System.err.printf("nodes length : %d, nestedwords length : %d\n", nodes.length, nestedWords.length());
		for (int i = 0; i < nestedWords.length(); i++) {
			try {
				System.err.println(nestedWords.getCallPosition(i));
			} catch (Exception e) {
				try {
					System.err.println(nestedWords.getReturnPosition(i));
				} catch (Exception f) {
					System.err.println("Null");
				}
			}
		}

		// for (int i = 0; i < nodes.length - 1; i++) {
		// if (nodes[i].getOutgoingEdgeLabel(nodes[i+1]) instanceof Return)
		// System.err.println("FoundReturnEdge at " + i);
		// else if (nodes[i].getOutgoingEdgeLabel(nodes[i+1]) instanceof Call)
		// System.err.println("FoundCallEdge at " + i);
		// }
	}

}
