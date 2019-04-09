/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.cfgpreprocessing;

import java.util.Collections;
import java.util.Set;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.GenericLabeledGraph;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * Graph representing a procedure with exactly one exit location and arbitrary many error locations.
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
	private final Set<IcfgLocation> mErrorNodes;

	public ProcedureGraph(final IcfgLocation entryNode, final IcfgLocation returnNode,
			final Set<IcfgLocation> errorNodes) {
		mEntryNode = entryNode;
		mExitNode = returnNode;
		mErrorNodes = errorNodes;
		mNodes.add(mEntryNode);
		mNodes.add(mExitNode);
		mNodes.addAll(mErrorNodes);
	}

	public ProcedureGraph(final IIcfg<IcfgLocation> icfg, final String procedureName) {
		this(icfg.getProcedureEntryNodes().get(procedureName), icfg.getProcedureExitNodes().get(procedureName),
				icfg.getProcedureErrorNodes().getOrDefault(procedureName, Collections.emptySet()));
	}

	public IcfgLocation getEntryNode() {
		return mEntryNode;
	}

	public IcfgLocation getExitNode() {
		return mExitNode;
	}

	public Set<IcfgLocation> getErrorNodes() {
		return mErrorNodes;
	}
	
	public Stream<IcfgLocation> errorAndExitNodesStream() {
		return Stream.concat(Stream.of(mExitNode), mErrorNodes.stream());
	}
}
