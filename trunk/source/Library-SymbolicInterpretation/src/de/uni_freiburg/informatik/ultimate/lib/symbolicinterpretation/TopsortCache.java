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
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDag;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDagNode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.TopologicalSorter;

public class TopsortCache {

	private final Map<RegexDag<IIcfgTransition<IcfgLocation>>, List<RegexDagNode<IIcfgTransition<IcfgLocation>>>>
			mCache = new HashMap<>();

	public List<RegexDagNode<IIcfgTransition<IcfgLocation>>> topsort(
			final RegexDag<IIcfgTransition<IcfgLocation>> dag) {
		return mCache.computeIfAbsent(dag, TopsortCache::compute);
	}

	private static List<RegexDagNode<IIcfgTransition<IcfgLocation>>> compute(
			final RegexDag<IIcfgTransition<IcfgLocation>> dag) {
		return new TopologicalSorter<RegexDagNode<IIcfgTransition<IcfgLocation>>>(RegexDagNode::getOutgoingNodes)
				.topologicalOrdering(dag.collectNodes())
				.orElseThrow(() -> new IllegalStateException("\"Dag\" had a cycle:\n" + dag));
	}
}
