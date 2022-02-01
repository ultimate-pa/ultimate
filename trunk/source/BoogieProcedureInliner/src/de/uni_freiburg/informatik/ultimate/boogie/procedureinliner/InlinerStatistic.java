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
package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphEdgeLabel;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphNode;

/**
 * Minor statistics about the running inlining process.
 * Used for information on (possible) timeout while inlining.
 */
public class InlinerStatistic {

	private final Map<String, CallGraphNode> mCallGraph;
	private int mCallsInlined = 0;
	private int mStatementsFlattened = 0;

	public InlinerStatistic (Map<String, CallGraphNode> callGraph) {
		mCallGraph = callGraph;
	}
	
	public void incrementStatementsFlattened() {
		++mStatementsFlattened;
	}
	
	/**
	 * Also calls {@link InlinerStatistic#incrementStatementsFlattened()},
	 * since a call is a statement and the inlining flattened it.
	 */
	public void incrementCallsInlined() {
		incrementStatementsFlattened();
		++mCallsInlined;
	}

	public int numberOfProcedures() {
		return mCallGraph.size();
	}
	
	public int numberOfCallGraphEdges() {
		int edges = 0;
		for (final CallGraphNode node : mCallGraph.values()) {
			edges += node.getOutgoingEdgeLabels().size();
		}
		return edges;
	}
	
	public int numberOfCallGraphEdgesWithInlineFlag() {
		int flaggedEdges = 0;
		for (final CallGraphNode node : mCallGraph.values()) {
			for (final CallGraphEdgeLabel edgeLabel : node.getOutgoingEdgeLabels()) {
				if (edgeLabel.getInlineFlag()) {
					++flaggedEdges;
				}
			}
		}
		return flaggedEdges;
	}

	@Override
	public String toString() {
		String s = "procedures = " + numberOfProcedures();
		s += ", calls = " + numberOfCallGraphEdges();
		s += ", calls flagged for inlining = " + numberOfCallGraphEdgesWithInlineFlag();
		s += ", calls inlined = " + mCallsInlined;
		s += ", statements flattened = " + mStatementsFlattened;
		return s;
	}
}
