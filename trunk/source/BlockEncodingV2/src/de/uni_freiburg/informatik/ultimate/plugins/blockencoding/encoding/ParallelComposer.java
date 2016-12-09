/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BlockEncodingV2 plug-in.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncodingV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncodingV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncodingV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class ParallelComposer extends BaseBlockEncoder<IcfgLocation> {
	
	private int mEdgesRemoved;
	private final IcfgEdgeBuilder mEdgeBuilder;
	
	public ParallelComposer(final IcfgEdgeBuilder edgeBuilder, final IUltimateServiceProvider services) {
		super(services);
		mEdgesRemoved = 0;
		mEdgeBuilder = edgeBuilder;
	}
	
	@Override
	protected BasicIcfg<IcfgLocation> createResult(final BasicIcfg<IcfgLocation> icfg) {
		mLogger.info("Creating parallel compositions");
		
		final Deque<IcfgLocation> nodes = new ArrayDeque<>();
		final Set<IcfgLocation> closed = new HashSet<>();
		
		nodes.addAll(icfg.getInitialNodes());
		
		while (!nodes.isEmpty()) {
			final IcfgLocation current = nodes.removeFirst();
			if (!closed.add(current)) {
				continue;
			}
			
			final List<IcfgEdge> outEdges = current.getOutgoingEdges();
			final Map<IcfgLocation, List<CodeBlock>> map = new HashMap<>();
			outEdges.stream().forEach(a -> acc(map, a));
			
			for (final Entry<IcfgLocation, List<CodeBlock>> partition : map.entrySet()) {
				final IcfgLocation target = partition.getKey();
				nodes.add(target);
				final List<CodeBlock> edges = partition.getValue();
				final int edgeSize = edges.size();
				if (edgeSize > 1) {
					mEdgeBuilder.constructParallelComposition((BoogieIcfgLocation) current, (BoogieIcfgLocation) target,
							edges);
					edges.stream().forEach(ParallelComposer::disconnect);
					mEdgesRemoved += edgeSize;
				}
			}
		}
		return icfg;
	}
	
	private static Map<IcfgLocation, List<CodeBlock>> acc(final Map<IcfgLocation, List<CodeBlock>> map,
			final IcfgEdge e) {
		final BoogieIcfgLocation target = (BoogieIcfgLocation) e.getTarget();
		final List<CodeBlock> set = map.get(target);
		if (set == null) {
			final List<CodeBlock> newSet = new ArrayList<>();
			newSet.add((CodeBlock) e);
			map.put(target, newSet);
		} else {
			set.add((CodeBlock) e);
		}
		return map;
	}
	
	private static void disconnect(final IcfgEdge edge) {
		edge.disconnectSource();
		edge.disconnectTarget();
	}
	
	@Override
	public boolean isGraphStructureChanged() {
		return mEdgesRemoved > 0;
	}
}
