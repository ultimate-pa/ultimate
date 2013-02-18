package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util;

import java.util.HashMap;
import java.util.HashSet;
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
    private HashMap<String, HashSet<String>> graph;
    /**
     * The SCCs to return.
     */
    private HashSet<HashSet<String>> sccs;
    /**
     * The Tarjan indices for the vertices.
     */
    private HashMap<String, Integer> indices;
    /**
     * The Tarjan lowlinks for the vertices.
     */
    private HashMap<String, Integer> lowLink;

    /**
     * Calculate SCCs for the given graph.
     * 
     * @param graph
     *            the graph to work on
     * @return a list of SCCs
     */
    public HashSet<HashSet<String>> getSCCs(
            final HashMap<String, HashSet<String>> graph) {
        if (graph == null || graph.values().contains(null)) {
            throw new IllegalArgumentException();
        }
        this.graph = graph;
        this.maxIndex = 0;
        this.stack = new Stack<String>();
        this.sccs = new HashSet<HashSet<String>>();
        this.indices = new HashMap<String, Integer>();
        this.lowLink = new HashMap<String, Integer>();
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
            HashSet<String> set = new HashSet<String>();
            String s;
            do {
                s = this.stack.pop();
                set.add(s);
            } while (!s.equals(v));
            sccs.add(set);
        }
    }
}
