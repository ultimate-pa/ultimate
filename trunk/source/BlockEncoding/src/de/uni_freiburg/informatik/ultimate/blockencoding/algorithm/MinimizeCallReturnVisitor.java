/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.algorithm;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.visitor.IMinimizationVisitor;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.ConjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.DisjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IBasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockendcoding.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 * This visitor is responsible, to merge call and return edges in the graph. So
 * if a method is loop-free and has no error location, it is possible to
 * minimize it and replace it with the summary edge, for every call in the
 * program. <br>
 * <b>Note1:</b> It is not recommended to execute this visitor in parallel,
 * because there multiple dependencies among the method calls. <br>
 * <b>Note2:</b> It is possible that by following the call-edges we can add up
 * in a possible cycle, if this is the case, we stop the minimization there.
 * 
 * @author Stefan Wissert
 * 
 */
public class MinimizeCallReturnVisitor implements IMinimizationVisitor {

	private static Logger s_Logger;

	private MinimizeBranchVisitor mbv;

	private HashSet<MinimizedNode> actualCallStack;

	/**
	 * 
	 */
	public MinimizeCallReturnVisitor() {
		mbv = new MinimizeBranchVisitor();
		s_Logger = UltimateServices.getInstance().getLogger(
				Activator.s_PLUGIN_ID);
	}

	@Override
	public void visitNode(MinimizedNode node) {
		actualCallStack = new HashSet<MinimizedNode>();
		internalVisitNode(node);
	}

	/**
	 * Internal recursive visit method.
	 * 
	 * @param node
	 *            the Method-Entry-Node to inspect.
	 */
	private void internalVisitNode(MinimizedNode node) {
		// By calling this method, the parameter node is the the method head
		// --> we check the edges for Call-Edges
		actualCallStack.add(node);
		IMinimizedEdge substituteEdge = null;
		// we need a copy of the incoming edge list
		List<IMinimizedEdge> incomingEdgeList = new ArrayList<IMinimizedEdge>(
				node.getMinimalIncomingEdgeLevel());
		for (IMinimizedEdge edge : incomingEdgeList) {
			if (edge.isBasicEdge()
					&& ((IBasicEdge) edge).getOriginalEdge() instanceof Call) {
				// now we found an Call-Edge, so this method is called
				// next step is to try if we can minimize the whole method, and
				// substitute the summary edge by a concrete formula
				if (substituteEdge == null) {
					substituteEdge = tryToMergeMethod(node);
					// if the method is not mergeable we return null
					if (substituteEdge == null) {
						return;
					}
					// if our substitueEdge is an Call-Edge, we try do resolve
					// it recursively, if this is not possible we do not
					// minimize further (possible cycles in the call graph)
					while (substituteEdge != null
							&& substituteEdge.isBasicEdge()
							&& ((IBasicEdge) substituteEdge).getOriginalEdge() instanceof Call) {
						// so we found a Call-Edge, we try to minimize it
						// recursively
						// Check if we already visited this metod entry node on
						// the call stack
						if (actualCallStack
								.contains(substituteEdge.getTarget())) {
							s_Logger.debug("Detected a Cycle in the Call-Stack :"
									+ substituteEdge.getTarget()
									+ " / "
									+ actualCallStack);
							// we have a cycle in the call stack, so we stop the
							// minimization here
							substituteEdge = null;
							break;
						}
						internalVisitNode(substituteEdge.getTarget());
						substituteEdge = tryToMergeMethod(node);
					}
					// if the method is not mergeable we return null
					if (substituteEdge == null) {
						return;
					}
				}
				// We build the edge Call + Substitute,
				// the Return is still missing!
				substituteEdge = new ConjunctionEdge(edge, substituteEdge);
				minimizeCallReturnEdge(((IBasicEdge) edge), substituteEdge);
				// Since we have replaced the call-edge, we create a new
				// incoming edge level for the Method-Entry-Node
				ArrayList<IMinimizedEdge> incomingListLevel = new ArrayList<IMinimizedEdge>(
						node.getMinimalIncomingEdgeLevel());
				incomingListLevel.remove(edge);
				node.addNewIncomingEdgeLevel(incomingListLevel);
				mbv.visitNode(edge.getSource());
			}
		}
		// No Call-Edges, nothing to do here
		return;
	}

	/**
	 * @param node
	 *            method head to inspect
	 * @return the already minimized edge or an Call-Edge for further
	 *         minimization
	 */
	private IMinimizedEdge tryToMergeMethod(MinimizedNode node) {
		// now we have to check, if it is possible to minimize the method
		if (node.getOutgoingEdges().size() == 1) {
			IMinimizedEdge edge = (IMinimizedEdge) node.getOutgoingEdges().get(
					0);
			// so we check if the method is already minimized to one edge
			boolean hasReturnEdges = false;
			for (IMinimizedEdge possibleReturnEdge : edge.getTarget()
					.getOutgoingEdges()) {
				if (possibleReturnEdge.isBasicEdge()) {
					IBasicEdge basicEdge = (IBasicEdge) possibleReturnEdge;
					if (basicEdge.getOriginalEdge() instanceof Call) {
						return basicEdge;
					}
					if (basicEdge.getOriginalEdge() instanceof Return) {
						hasReturnEdges = true;
					}
				}
			}
			// there is no Return-Edge so we cannot minimize this method
			if (!hasReturnEdges) {
				return null;
			}
			return edge;
		} else if (node.getOutgoingEdges().size() == 2) {
			// Now we have a call edge directly in the method entry point
			// If we find an call edge we return it!
			for (IMinimizedEdge edge : node.getOutgoingEdges()) {
				if (edge.isBasicEdge()) {
					IBasicEdge basicEdge = (IBasicEdge) edge;
					if (basicEdge.getOriginalEdge() instanceof Call) {
						return basicEdge;
					}
				}
			}
		}
		return null;
	}

	/**
	 * If we can substitute a method by one edge, this method will do this. It
	 * searches the corresponding Return-Edge for an Call-Edge and composite it
	 * in a Sequential way. The Summary-Edge is included in a Parallel Way. <br>
	 * The new substitution edges are included in at the corresponding nodes.
	 * 
	 * @param callEdge
	 * @param substitute
	 */
	private void minimizeCallReturnEdge(IBasicEdge callEdge,
			IMinimizedEdge substitute) {
		MinimizedNode callingNode = (MinimizedNode) callEdge.getSource();
		// Note: It is possible that callingNode has more than two outgoing
		// edges!
		// --> we have to care for the edges which should be part of the new
		// outgoing edge level
		ArrayList<IMinimizedEdge> callNodeOutEdges = new ArrayList<IMinimizedEdge>(
				callingNode.getMinimalOutgoingEdgeLevel());
		// We first remove the call node from this list
		callNodeOutEdges.remove(callEdge);

		// We to find the corresponding SummaryEdge
		IBasicEdge summaryEdge = null;
		for (IMinimizedEdge edge : callingNode.getMinimalOutgoingEdgeLevel()) {
			if (edge.isBasicEdge()
					&& ((IBasicEdge) edge).getOriginalEdge() instanceof Summary) {
				summaryEdge = (IBasicEdge) edge;
				break;
			}
		}
		if (summaryEdge == null) {
			throw new IllegalStateException("There should be an summaryEdge");
		}
		// We remove also the summary edge of the new outgoing edge level
		callNodeOutEdges.remove(summaryEdge);

		// Now we search the corresponding ReturnEdge
		IBasicEdge returnEdge = null;
		MinimizedNode returningNode = (MinimizedNode) summaryEdge.getTarget();
		for (IMinimizedEdge edge : returningNode.getMinimalIncomingEdgeLevel()) {
			if (edge.isBasicEdge()
					&& ((IBasicEdge) edge).getOriginalEdge() instanceof Return) {
				returnEdge = (IBasicEdge) edge;
				break;
			}
		}
		if (returnEdge == null) {
			throw new IllegalStateException("There should be an returnEdge");
		}
		s_Logger.debug("Add Return: " + substitute + " / " + returnEdge);
		// We build our new Substitute Edge Call + Sub + Return
		// Later Call and Return have to be replaced (to true)!
		substitute = new ConjunctionEdge(substitute, returnEdge);
		// now we add the Summary to the substitution (to false)!
		s_Logger.debug("Handle Summary: " + summaryEdge + " / " + substitute);
		substitute = new DisjunctionEdge(summaryEdge, substitute);
		// Now substitute the Call / Return / Summary edges
		callNodeOutEdges.add(substitute);
		callingNode.addNewOutgoingEdgeLevel(callNodeOutEdges);
		// We have to replace the Return Edge on both sides
		List<IMinimizedEdge> outgoingList = new ArrayList<IMinimizedEdge>(
				returnEdge.getSource().getMinimalOutgoingEdgeLevel());
		outgoingList.remove(returnEdge);
		returnEdge.getSource().addNewOutgoingEdgeLevel(outgoingList);

		if (returningNode.getMinimalIncomingEdgeLevel().size() > 2) {
			s_Logger.warn("Node at this point should only have Return and"
					+ " Summary as incoming edges!");
		}

		returningNode.addNewIncomingEdgeLevel(Collections
				.singletonList(substitute));

	}
}
