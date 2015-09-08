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
import java.util.Stack;

/**
 * Class to calculate SCCs using tarjans algorithm.
 * 
 * @author Markus Lindenmann
 * @date 08.08.2012
 */
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
    private LinkedHashMap<String, LinkedHashSet<String>> graph;
    /**
     * The SCCs to return.
     */
    private LinkedHashSet<LinkedHashSet<String>> sccs;
    /**
     * The Tarjan indices for the vertices.
     */
    private LinkedHashMap<String, Integer> indices;
    /**
     * The Tarjan lowlinks for the vertices.
     */
    private LinkedHashMap<String, Integer> lowLink;

    /**
     * Calculate SCCs for the given graph.
     * 
     * @param graph
     *            the graph to work on
     * @return a list of SCCs
     */
    public LinkedHashSet<LinkedHashSet<String>> getSCCs(
            final LinkedHashMap<String, LinkedHashSet<String>> graph) {
        if (graph == null || graph.values().contains(null)) {
            throw new IllegalArgumentException();
        }
        this.graph = graph;
        this.maxIndex = 0;
        this.stack = new Stack<String>();
        this.sccs = new LinkedHashSet<LinkedHashSet<String>>();
        this.indices = new LinkedHashMap<String, Integer>();
        this.lowLink = new LinkedHashMap<String, Integer>();
        for (String v : this.graph.keySet()) {
            if (!this.indices.containsKey(v)) {
                this.strongConnect(v);
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
    private void strongConnect(String v) {
        if (!this.graph.containsKey(v)) {
            return; // skip undeclared methods!
        }
        assert (!this.indices.containsKey(v));
        assert (!this.indices.containsKey(v));
        this.indices.put(v, this.maxIndex);
        this.lowLink.put(v, this.maxIndex);
        this.maxIndex++;
        this.stack.push(v);
        for (String s : this.graph.get(v)) {
            if (!this.graph.containsKey(s)) {
                stack.remove(s);
                continue; // skip undeclared methods!
            }
            if (!this.indices.containsKey(s)) {
                this.strongConnect(s);
                this.lowLink.put(v,
                        Math.min(this.lowLink.get(v), this.lowLink.get(s)));
            } else if (stack.contains(s)) {
                this.lowLink.put(v,
                        Math.min(this.lowLink.get(v), this.indices.get(s)));
            }
        }
        if (this.lowLink.get(v).equals(this.indices.get(v))) {
            LinkedHashSet<String> set = new LinkedHashSet<String>();
            String s;
            do {
                s = this.stack.pop();
                set.add(s);
            } while (!s.equals(v));
            sccs.add(set);
        }
    }
}
