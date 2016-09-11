/*
 * Copyright (C) 2013-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BlockEncoding plug-in.
 * 
 * The ULTIMATE BlockEncoding plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BlockEncoding plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncoding plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncoding plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncoding plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.algorithm;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.visitor.IMinimizationVisitor;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.ConjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.ShortcutErrEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IBasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
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

	private final ILogger mLogger;

	private HashSet<MinimizedNode> mActualCallStack;

	/**
	 * We need this list of nodes where we replaced an call edge by substitution.
	 * Maybe it is possible to minimize them again, in a later step.
	 */
	private final HashSet<MinimizedNode> nodesForReVisit;
	
	private final AbstractMinimizationVisitor amVisitor;

	/**
	 * 
	 */
	public MinimizeCallReturnVisitor(final ILogger logger, final AbstractMinimizationVisitor amVisitor) {
		mLogger = logger;
		nodesForReVisit = new HashSet<MinimizedNode>();
		this.amVisitor = amVisitor;
	}

	@Override
	public void visitNode(final MinimizedNode node) {
		mActualCallStack = new HashSet<MinimizedNode>();
		internalVisitNode(node);
	}

	/**
	 * Internal recursive visit method.
	 * 
	 * @param node
	 *            the Method-Entry-Node to inspect.
	 */
	private void internalVisitNode(final MinimizedNode node) {
		// By calling this method, the parameter node is the the method head
		// --> we check the edges for Call-Edges
		mActualCallStack.add(node);
		IMinimizedEdge substituteEdge = null;
		IMinimizedEdge[] edges = null;
		// we need a copy of the incoming edge list
		final List<IMinimizedEdge> incomingEdgeList = new ArrayList<IMinimizedEdge>(
				node.getMinimalIncomingEdgeLevel());
		for (final IMinimizedEdge edge : incomingEdgeList) {
			// Check if predecessor has successors. This is not the case
			// if predecessor is deadcode.
			if (predecessorSuccIsNull(edge)) {
				continue;
			}
			if (edge.isBasicEdge()
					&& ((IBasicEdge) edge).getOriginalEdge() instanceof Call) {
				// now we found an Call-Edge, so this method is called
				// next step is to try if we can minimize the whole method, and
				// substitute the summary edge by a concrete formula
				if (substituteEdge == null) {
					edges = tryToMergeMethod(node);
					// if the method is not mergeable we return null
					if (edges == null) {
						return;
					}
					// We get the substitution and the shortcut to the error
					// locations, which can be added directly
					substituteEdge = edges[0];
					if (edges.length > 1) {
						directEdgesToErrorLocation(edge, edges);
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
						if (mActualCallStack
								.contains(substituteEdge.getTarget())) {
							mLogger.debug("Detected a Cycle in the Call-Stack :"
									+ substituteEdge.getTarget()
									+ " / "
									+ mActualCallStack);
							// we have a cycle in the call stack, so we stop the
							// minimization here
							substituteEdge = null;
							break;
						}
						internalVisitNode(substituteEdge.getTarget());
						edges = tryToMergeMethod(node);
						if (edges == null) {
							substituteEdge = null;
						} else {
							substituteEdge = edges[0];
							if (edges.length > 1) {
								directEdgesToErrorLocation(edge, edges);
							}
						}
					}
					// if the method is not mergeable we return null
					if (substituteEdge == null) {
						return;
					}
				} else {
					// if we already found a substitution edge, we need to also
					// insert the shortcuts to the error locations
					directEdgesToErrorLocation(edge, edges);
				}
				// We build the edge Call + Substitute,
				// the Return is still missing!
				// Remark 06.06.2013: Call + Substitute builds a new edge!
				final ConjunctionEdge callAndSubstitute = new ConjunctionEdge(edge, substituteEdge);
				minimizeCallReturnEdge(((IBasicEdge) edge), callAndSubstitute);
				// so we replaced an call here, so we may have to revisit this node
				nodesForReVisit.add(amVisitor.getCorrespondingStartNode(edge.getSource()));
				// Since we have replaced the call-edge, we create a new
				// incoming edge level for the Method-Entry-Node
				final ArrayList<IMinimizedEdge> incomingListLevel = new ArrayList<IMinimizedEdge>(
						node.getMinimalIncomingEdgeLevel());
				incomingListLevel.remove(edge);
				node.addNewIncomingEdgeLevel(incomingListLevel);
			}
		}
		// No Call-Edges, nothing to do here
		return;
	}
	
	/**
	 * Does the predecessor of edge have successors? This is not the case if the
	 * predecessor is deadcode, but edge was added because it is a call.
	 * Added by Matthias 24.10.2013
	 */
	private boolean predecessorSuccIsNull(final IMinimizedEdge edge) {
		final MinimizedNode predecessor = edge.getSource();
		return predecessor.getOutgoingEdges() == null;
	}

	/**
	 * This method is used to generate shortcuts (direct edges) to error
	 * locations, if this is possible. Basically we need to add a new entry to
	 * the outgoing edges of the callEdge.getSource() and new incoming edges for
	 * the respective error location.
	 * 
	 * @param callEdge
	 * @param subEdges
	 */
	private void directEdgesToErrorLocation(final IMinimizedEdge callEdge,
			final IMinimizedEdge[] subEdges) {
		// First step is to add the new edges to callEdge.getSource->Outgoing
		final ArrayList<IMinimizedEdge> newOutEdgeLevel = new ArrayList<IMinimizedEdge>(
				callEdge.getSource().getOutgoingEdges());
		final ArrayList<IMinimizedEdge> shortcuts = new ArrayList<IMinimizedEdge>();
		for (int i = 1; i < subEdges.length; i++) {
			final ShortcutErrEdge shortcut = new ShortcutErrEdge(callEdge,
					subEdges[i]);
			newOutEdgeLevel.add(shortcut);
			shortcuts.add(shortcut);
		}
		callEdge.getSource().addNewOutgoingEdgeLevel(newOutEdgeLevel, null);
		// Second step is to add the new edges to the incoming set of the error
		// locations
		for (final IMinimizedEdge shortcutEdge : shortcuts) {
			final ArrayList<IMinimizedEdge> newIncomingEdgeLevel = new ArrayList<IMinimizedEdge>(
					shortcutEdge.getTarget().getIncomingEdges());
			newIncomingEdgeLevel.add(shortcutEdge);
			shortcutEdge.getTarget().addNewIncomingEdgeLevel(
					newIncomingEdgeLevel);
		}

	}

	/**
	 * @param node
	 *            method head to inspect
	 * @return the already minimized edge or an Call-Edge for further
	 *         minimization
	 */
	private IMinimizedEdge[] tryToMergeMethod(final MinimizedNode node) {
		// Remark 04.04.2013: It may be possible that one incoming edge is a
		// self-loop, if one incoming edge is not a call or root edge should be
		// sufficient as check
		for (final IMinimizedEdge edge : node.getIncomingEdges()) {
			if (!edge.isBasicEdge()) {
				return null;
			}
		}

		// now we have to check, if it is possible to minimize the method
		// We either have a direct shortcut to complete minimize the function or
		// we have the shortcut and various ways to error locations, which also
		// can be minimized
		// Now we have a call edge directly in the method entry point
		// If we find an call edge we return it!
		IMinimizedEdge subsituteEdge = null;
		final ArrayList<IMinimizedEdge> errorLocationEdges = new ArrayList<IMinimizedEdge>();
		for (final IMinimizedEdge edge : node.getOutgoingEdges()) {
			// If the oldVar-Operator is involved we do not minimize such
			// methods! Due to a problem while composing with
			// SequentialComposition, there is a scoping problem with old(g)
			if (edge.isOldVarInvolved()) {
				return null;
			}
			if (edge.isBasicEdge()) {
				final IBasicEdge basicEdge = (IBasicEdge) edge;
				if (basicEdge.getOriginalEdge() instanceof Call) {
					return new IMinimizedEdge[] { basicEdge };
				}
			}
			// Another possibility is that we have a direct way to an error
			// location, this is possible to minimize
			if (edge.getTarget().getOriginalNode().isErrorLocation()) {
				errorLocationEdges.add(edge);
			}
			for (final IMinimizedEdge possibleReturnEdge : edge.getTarget()
					.getOutgoingEdges()) {
				if (possibleReturnEdge.isBasicEdge()) {
					final IBasicEdge basicEdge = (IBasicEdge) possibleReturnEdge;
					if (basicEdge.getOriginalEdge() instanceof Call) {
						return new IMinimizedEdge[] { basicEdge };
					}
					if (basicEdge.getOriginalEdge() instanceof Return) {
						subsituteEdge = edge;
						break;
					}
				}
			}
		}
		// if we have a substitute and a list of possible error locations, we
		// create the shortcuts for them, in all other cases we do not minimize
		// further
		if (subsituteEdge != null
				&& errorLocationEdges.size() == (node.getOutgoingEdges().size() - 1)) {
			final ArrayList<IMinimizedEdge> edges = new ArrayList<IMinimizedEdge>();
			edges.add(subsituteEdge);
			edges.addAll(errorLocationEdges);
			return edges.toArray(new IMinimizedEdge[edges.size()]);
		} else if (subsituteEdge != null) {
			return new IMinimizedEdge[] { subsituteEdge };
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
	private void minimizeCallReturnEdge(final IBasicEdge callEdge,
			IMinimizedEdge substitute) {
		final MinimizedNode callingNode = callEdge.getSource();
		// Note: It is possible that callingNode has more than two outgoing
		// edges!
		// --> we have to care for the edges which should be part of the new
		// outgoing edge level
		final ArrayList<IMinimizedEdge> callNodeOutEdges = new ArrayList<IMinimizedEdge>(
				callingNode.getMinimalOutgoingEdgeLevel());
		// We first remove the call node from this list
		callNodeOutEdges.remove(callEdge);

		// We to find the corresponding SummaryEdge
		IBasicEdge summaryEdge = null;
		for (final IMinimizedEdge edge : callingNode.getMinimalOutgoingEdgeLevel()) {
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
		final MinimizedNode returningNode = summaryEdge.getTarget();
		for (final IMinimizedEdge edge : returningNode.getMinimalIncomingEdgeLevel()) {
			if (edge.isBasicEdge()
					&& ((IBasicEdge) edge).getOriginalEdge() instanceof Return) {
				returnEdge = (IBasicEdge) edge;
				break;
			}
		}
		if (returnEdge == null) {
			throw new IllegalStateException("There should be an returnEdge");
		}
		mLogger.debug("Add Return: " + substitute + " / " + returnEdge);
		// We build our new Substitute Edge Call + Sub + Return
		// Later Call and Return have to be replaced (to true)!
		substitute = new ConjunctionEdge(substitute, returnEdge);
		// now we add the Summary to the substitution (to false)!
		mLogger.debug("Handle Summary: " + summaryEdge + " / " + substitute);
		//substitute = new DisjunctionEdge(summaryEdge, substitute);
		// Now substitute the Call / Return / Summary edges
		callNodeOutEdges.add(substitute);
		callingNode.addNewOutgoingEdgeLevel(callNodeOutEdges, null);
		// We have to replace the Return Edge on both sides
		final List<IMinimizedEdge> outgoingList = new ArrayList<IMinimizedEdge>(
				returnEdge.getSource().getMinimalOutgoingEdgeLevel());
		outgoingList.remove(returnEdge);
		returnEdge.getSource().addNewOutgoingEdgeLevel(outgoingList, substitute);

		if (returningNode.getMinimalIncomingEdgeLevel().size() > 2) {
			mLogger.warn("Node at this point should only have Return and"
					+ " Summary as incoming edges!");
		}

		returningNode.addNewIncomingEdgeLevel(Collections
				.singletonList(substitute));

	}

	/**
	 * @return the nodesForReVisit
	 */
	public HashSet<MinimizedNode> getNodesForReVisit() {
		return nodesForReVisit;
	}
}
