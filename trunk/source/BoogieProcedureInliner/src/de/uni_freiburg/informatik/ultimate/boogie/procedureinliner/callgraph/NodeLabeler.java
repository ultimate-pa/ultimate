/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogieProcedureInliner plug-in.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieProcedureInliner plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieProcedureInliner plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogieProcedureInliner plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

/**
 * Labels the nodes of a Boogie call graph.
 * <p>
 * Note, that call-foralls aren't treated other than normal calls.
 * This is not a real problem, but might be inefficient in some (constructed) cases.
 * 
 * @see CallGraphNodeLabel
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class NodeLabeler {

	private final Collection<String> mEntryProcedures;
	
	private Map<String, CallGraphNode> mCallGraph;
	private Set<CallGraphEdgeLabel> mVisitedEdges;
	private Set<String> mEntryAndReEntryProcedures;

	public NodeLabeler(Collection<String> entryPorcedures) {
		mEntryProcedures = entryPorcedures;
	}

	/**
	 * Sets the node labels for a call graph.
	 * <p>
	 * The inline flags for the call graph edges should have their final value assigned,
	 * because the node labels depend on the inline flags.
	 * 
	 * @param callGraph Boogie call graph whose inline flags don't change anymore.
	 * 
	 * @return Identifiers from all existing procedures, marked as entry or re-entry procedures.
	 * 
	 * @see CallGraphNodeLabel
	 */
	public Set<String> label(Map<String, CallGraphNode> callGraph) {
		reset();
		mCallGraph = callGraph;
		for (final String entryId : mEntryProcedures) {
			final CallGraphNode entryNode = callGraph.get(entryId);
			if (entryNode == null) {
				// user specified a non-existent procedure as a possible entry point
				continue;
			}
			entryNode.setLabel(CallGraphNodeLabel.ENTRY);
			mEntryAndReEntryProcedures.add(entryId);
			visitChildren(entryNode);
		}
		labelNonLabeledNodesAsDead();
		return mEntryAndReEntryProcedures;
	}

	private void reset() {
		mCallGraph = null;
		mVisitedEdges = new HashSet<>();
		mEntryAndReEntryProcedures = new HashSet<>();
	}

	private void visitChildren(CallGraphNode source) {
		final Iterator<CallGraphEdgeLabel> arcs = source.getOutgoingEdgeLabels().iterator();
		final Iterator<CallGraphNode> targets = source.getOutgoingNodes().iterator();
		while (arcs.hasNext() && targets.hasNext()) {
			final CallGraphNode target = targets.next();
			final CallGraphEdgeLabel arc = arcs.next();
			final boolean arcAlreadyVisited = !mVisitedEdges.add(arc);
			final boolean targetNodeAlreadyLabeled = target.getLabel() != null;
			if (arcAlreadyVisited || targetNodeAlreadyLabeled) {
				continue;
			}
			if (!arc.getInlineFlag()) {
				target.setLabel(CallGraphNodeLabel.RE_ENTRY);
				mEntryAndReEntryProcedures.add(target.getId());
			}
			visitChildren(target);
		}
	}
	
	private void labelNonLabeledNodesAsDead() {
		for (final CallGraphNode node : mCallGraph.values()) {
			if (node.getLabel() == null) {
				node.setLabel(CallGraphNodeLabel.DEAD);
			}
		}
	}

}
