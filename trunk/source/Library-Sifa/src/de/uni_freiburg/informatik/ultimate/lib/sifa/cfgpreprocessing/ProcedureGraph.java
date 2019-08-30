/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.cfgpreprocessing;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.GenericLabeledGraph;

/**
 * Graph representing a procedure with exactly one exit location and arbitrary many locations of interest.
 * <p>
 * The nodes of this graph are just labels which happen to be nodes from another graph structure (ICFG).
 * That other graph structure is unrelated to this graph.
 * This graph can only be modified via this class. Do <b>not</b> try to modify this graph by calling
 * methods of the nodes; those have no knowledge of this graph structure.
 * Likewise the edge labels happen to be edges them self but are not related to this graph structure.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class ProcedureGraph extends GenericLabeledGraph<IcfgLocation, IIcfgTransition<IcfgLocation>> {

	private final IcfgLocation mEntryNode;
	private final IcfgLocation mExitNode;

	/**
	 * Constructs the base for a new procedure graph. This graph starts only with some disconnected nodes.
	 * use {@link #addEdge(IcfgLocation, IIcfgTransition, IcfgLocation)} to add edges and more nodes.
	 * @param entryNode Entry node of the procedure from inside the icfg
	 * @param exitNode Exit node of the procedure from inside the icfg
	 */
	public ProcedureGraph(final IcfgLocation entryNode, final IcfgLocation exitNode) {
		mEntryNode = entryNode;
		mExitNode = exitNode;
		mNodes.add(mEntryNode);
		mNodes.add(mExitNode);
	}

	/**
	 * Constructs the base for a new procedure graph. This is <b>not</b> the final procedure graph
	 * for the given function. Use {@link ProcedureGraphBuilder} to construct a full graph.
	 * @param icfg An interprocedural control flow graph
	 * @param procedureName An implemented procedure from the ICFG for which a procedure graph will be constructed
	 */
	public ProcedureGraph(final IIcfg<IcfgLocation> icfg, final String procedureName) {
		this(icfg.getProcedureEntryNodes().get(procedureName), icfg.getProcedureExitNodes().get(procedureName));
	}

	public IcfgLocation getEntryNode() {
		return mEntryNode;
	}

	public IcfgLocation getExitNode() {
		return mExitNode;
	}
}
