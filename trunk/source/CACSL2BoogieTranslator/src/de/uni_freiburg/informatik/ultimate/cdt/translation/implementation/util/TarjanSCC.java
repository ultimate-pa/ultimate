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

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

/**
 * Class to calculate SCCs using tarjans algorithm.
 *
 * @author Markus Lindenmann
 * @date 08.08.2012
 *
 * (Alexander Nutz Feb 2018:) deprecated, use class de.uni_freiburg.informatik.ultimate.util.scc.SccComputation instead
 */
@Deprecated
public final class TarjanSCC {
    /**
     * The maximum index for Tarjans algorithm.
     */
    private int maxIndex;
    /**
     * The stack for Tarjans algorithm.
     */
    private Stack<String> stack;
    /**
     * The graph to work on. Map of vertex id to its successor ids.
     */
    private Map<String, Set<String>> graph;
    /**
     * The SCCs to return.
     */
    private Set<Set<String>> sccs;
    /**
     * The Tarjan indices for the vertices.
     */
    private Map<String, Integer> indices;
    /**
     * The Tarjan lowlinks for the vertices.
     */
    private Map<String, Integer> lowLink;

    /**
     * Calculate SCCs for the given graph.
     *
     * @param graph
     *            the graph to work on
     * @return a list of SCCs
     */
    public Set<Set<String>> getSCCs(
            final Map<String, Set<String>> graph) {
        if (graph == null || graph.values().contains(null)) {
            throw new IllegalArgumentException();
        }
        this.graph = graph;
        maxIndex = 0;
        stack = new Stack<String>();
        sccs = new LinkedHashSet<Set<String>>();
        indices = new LinkedHashMap<String, Integer>();
        lowLink = new LinkedHashMap<String, Integer>();
        for (final String v : this.graph.keySet()) {
            if (!indices.containsKey(v)) {
                strongConnect(v);
            }
        }
        return sccs;
    }

    /**
     * Tarjans algorithm as described in <a href=
     * "http://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm"
     * >Wikipedia_en</a>.
     *
     * @param v
     *            the vertex to visit.
     */
    private void strongConnect(final String v) {
        if (!graph.containsKey(v)) {
            return; // skip undeclared methods!
        }
        assert (!indices.containsKey(v));
        assert (!indices.containsKey(v));
        indices.put(v, maxIndex);
        lowLink.put(v, maxIndex);
        maxIndex++;
        stack.push(v);
        for (final String s : graph.get(v)) {
            if (!graph.containsKey(s)) {
                stack.remove(s);
                continue; // skip undeclared methods!
            }
            if (!indices.containsKey(s)) {
                strongConnect(s);
                lowLink.put(v,
                        Math.min(lowLink.get(v), lowLink.get(s)));
            } else if (stack.contains(s)) {
                lowLink.put(v,
                        Math.min(lowLink.get(v), indices.get(s)));
            }
        }
        if (lowLink.get(v).equals(indices.get(v))) {
            final LinkedHashSet<String> set = new LinkedHashSet<String>();
            String s;
            do {
                s = stack.pop();
                set.add(s);
            } while (!s.equals(v));
            sccs.add(set);
        }
    }
}
