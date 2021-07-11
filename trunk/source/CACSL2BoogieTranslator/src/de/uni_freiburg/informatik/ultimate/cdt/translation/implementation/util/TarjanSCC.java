/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputationNonRecursive;

/**
 * Class to calculate SCCs using Tarjans algorithm. An alternative with support for generic graphs is
 * {@link SccComputation} or {@link SccComputationNonRecursive}.
 *
 * @author Markus Lindenmann
 * @date 08.08.2012
 * @see SccComputation
 *
 */
public final class TarjanSCC {
	/**
	 * The maximum index for Tarjans algorithm.
	 */
	private int mMaxIndex;
	/**
	 * The stack for Tarjans algorithm.
	 */
	private Deque<String> mStack;
	/**
	 * The graph to work on. Map of vertex id to its successor ids.
	 */
	private Map<String, Set<String>> mGraph;
	/**
	 * The SCCs to return.
	 */
	private Set<ImmutableSet<String>> mSccs;
	/**
	 * The Tarjan indices for the vertices.
	 */
	private Map<String, Integer> mIndices;
	/**
	 * The Tarjan lowlinks for the vertices.
	 */
	private Map<String, Integer> mLowLink;

	/**
	 * Calculate SCCs for the given graph.
	 *
	 * @param graph
	 *            the graph to work on
	 * @return a list of SCCs
	 */
	public ImmutableSet<ImmutableSet<String>> getSCCs(final Map<String, Set<String>> graph) {
		if (graph == null || graph.values().contains(null)) {
			throw new IllegalArgumentException();
		}
		mGraph = graph;
		mMaxIndex = 0;
		mStack = new ArrayDeque<>();
		mSccs = new LinkedHashSet<>();
		mIndices = new LinkedHashMap<>();
		mLowLink = new LinkedHashMap<>();
		for (final String v : mGraph.keySet()) {
			if (!mIndices.containsKey(v)) {
				strongConnect(v);
			}
		}
		return ImmutableSet.of(mSccs);
	}

	/**
	 * Tarjans algorithm as described in
	 * <a href= "http://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm" >Wikipedia_en</a>.
	 *
	 * @param v
	 *            the vertex to visit.
	 */
	private void strongConnect(final String v) {
		if (!mGraph.containsKey(v)) {
			return; // skip undeclared methods!
		}
		mIndices.put(v, mMaxIndex);
		mLowLink.put(v, mMaxIndex);
		mMaxIndex++;
		mStack.push(v);
		for (final String s : mGraph.get(v)) {
			if (!mGraph.containsKey(s)) {
				mStack.remove(s);
				continue; // skip undeclared methods!
			}
			if (!mIndices.containsKey(s)) {
				strongConnect(s);
				mLowLink.put(v, Math.min(mLowLink.get(v), mLowLink.get(s)));
			} else if (mStack.contains(s)) {
				mLowLink.put(v, Math.min(mLowLink.get(v), mIndices.get(s)));
			}
		}
		if (mLowLink.get(v).equals(mIndices.get(v))) {
			final Set<String> set = new LinkedHashSet<>();
			String s;
			do {
				s = mStack.pop();
				set.add(s);
			} while (!s.equals(v));
			mSccs.add(ImmutableSet.of(set));
		}
	}
}
