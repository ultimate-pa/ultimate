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

import de.uni_freiburg.informatik.ultimate.models.structure.ILabeledEdgesMultigraph;

/**
 * Filter for labeled edges. This can be used inside graph algorithms to ignore unwanted edges without having to build a
 * modified copy of the graph.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 *
 * @param <V>
 *            Type of the graph nodes.
 * @param <L>
 *            Type of the graph edge labels.
 */
public interface ILabeledEdgesFilter<V extends ILabeledEdgesMultigraph<V, L, ?>, L> {

	/**
	 * Determines whether to use an outgoing edge or not.
	 * 
	 * @param source
	 *            Source node of the edge.
	 * @param outgoingEdgeLabel
	 *            Label of the edge.
	 * @param target
	 *            Target node of the edge.
	 * @return The edge should be used.
	 */
	public boolean accept(V source, L outgoingEdgeLabel, V target);
}
