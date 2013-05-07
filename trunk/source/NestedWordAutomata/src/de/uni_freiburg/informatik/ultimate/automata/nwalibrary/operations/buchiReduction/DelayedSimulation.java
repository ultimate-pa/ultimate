/**
 * Buchi automata state space reduction algorithm based on the following paper:
 * "Fair simulation relations, parity games and state space reduction for
 * Buchi automata" - Etessami, Wilke and Schuller.
 * 
 * Algorithm optimized to work using strongly connected components.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Player0Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Player1Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

/**
 * @author Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * @author Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * @date 16.01.2012
 */
public class DelayedSimulation<LETTER,STATE> {
    /**
     * Vertex set 0.
     */
    private HashSet<Player0Vertex<LETTER,STATE>> v0;
    /**
     * Vertex set 1.
     */
    private HashSet<Player1Vertex<LETTER,STATE>> v1;
    /**
     * Set of edges.
     */
    private HashMap<Vertex<LETTER,STATE>, HashSet<Vertex<LETTER, STATE>>> e;
    /**
     * Set if incoming edges to a vertex. The inverse edge set.
     */
    private HashMap<Vertex<LETTER,STATE>, HashSet<Vertex<LETTER, STATE>>> eI;
    /**
     * The number representing infinity for this game graph.
     */
    private int infinity;
    /**
     * The logger.
     */
    private static Logger s_Logger = UltimateServices.getInstance().getLogger(
            Activator.PLUGIN_ID);
    /**
     * Ultimate service for cancel operation.
     */
    private UltimateServices m_UltiServ = UltimateServices.getInstance();
    /**
     * Holding the result automaton.
     */
    NestedWordAutomaton<LETTER,STATE> result;
    /**
     * Whether or not to use SCCs.
     */
    private boolean useSCCs;

    /**
     * Constructor.
     * 
     * @param ba
     *            the input buchi automaton to reduce.
     * @param useSCCs
     *            whether to use strongly connected components
     * @throws OperationCanceledException
     */
    public DelayedSimulation(INestedWordAutomaton<LETTER,STATE> ba, boolean useSCCs)
            throws OperationCanceledException {
    	long startTime = System.currentTimeMillis();
        this.v0 = new HashSet<Player0Vertex<LETTER,STATE>>();
        this.v1 = new HashSet<Player1Vertex<LETTER,STATE>>();
        this.e = new HashMap<Vertex<LETTER,STATE>, HashSet<Vertex<LETTER, STATE>>>();
        this.eI = new HashMap<Vertex<LETTER,STATE>, HashSet<Vertex<LETTER, STATE>>>();
        this.useSCCs = useSCCs;
        generateGameGraph(ba);
        if(useSCCs) { // calculate reduction with SCC
            SccComputation scc = new SccComputation();
            Iterator<SCC> iter = scc.getSCCs().iterator();
            while(iter.hasNext()) {
                SCC s = iter.next();
                iter.remove();
                efficientLiftingAlgorithm(s.getSCCsVerticesWithPriorityOne()+1, s.getVertices());
            }
        } else { // calculate reduction w/o SCCs
            efficientLiftingAlgorithm(infinity, null);
        }
        clear();
        generateBuchiAutomaton(ba);
        long duration = System.currentTimeMillis() - startTime;
        s_Logger.info((this.useSCCs ? "SCC version" : "nonSCC version") + 
        		" took " + duration + " milliseconds.");
    }

    /**
     * Generates a GameGraph for a given Buchi automaton.
     * 
     * @param ba
     *            a Buchi automaton <b>without</b> dead ends
     * @throws OperationCanceledException
     */
    private void generateGameGraph(INestedWordAutomaton<LETTER,STATE> ba)
            throws OperationCanceledException {
        HashMap<STATE, HashMap<STATE, ArrayList<Player1Vertex<LETTER,STATE>>>> edgeH =
                new HashMap<STATE, HashMap<STATE, ArrayList<Player1Vertex<LETTER,STATE>>>>();
        // Calculate v1 [paper ref 10]
        for (STATE q0 : ba.getStates()) {
            edgeH.put(q0, new HashMap<STATE, ArrayList<Player1Vertex<LETTER,STATE>>>());
            for (STATE q1 : ba.getStates()) {
                edgeH.get(q0).put(q1, new ArrayList<Player1Vertex<LETTER,STATE>>(2));
                Player1Vertex<LETTER,STATE> v1e = new Player1Vertex<LETTER, STATE>(
                        (byte) 0, false, q0, q1);
                v1.add(v1e);
                edgeH.get(q0).get(q1).add(0, v1e);
                if (!ba.isFinal(q1)) {
                    v1e = new Player1Vertex<LETTER,STATE>((byte) 1, true, q0, q1);
                    v1.add(v1e);
                    edgeH.get(q0).get(q1).add(1, v1e);
                    infinity++;
                }
            }
            if (!m_UltiServ.continueProcessing()) {
                s_Logger.debug("Stopped in generateGameGraph/calculating v0 und v1");
                throw new OperationCanceledException();
            }
        }
        // Calculate v0 and edges [paper ref 10, 11, 12]
        for (STATE q0 : ba.getStates()) {
            for (STATE q1 : ba.getStates()) {
                for (LETTER s : ba.lettersInternalIncoming(q0)) {
                    if (ba.predInternal(q0, s).iterator().hasNext()) {
                        Player0Vertex<LETTER,STATE> v0e = new Player0Vertex<LETTER, STATE>(
                                (byte) 2, false, q0, q1, s);
                        v0.add(v0e);
                        // V0 -> V1 edges [paper ref 11]
                        for (STATE q2 : ba.succInternal(q1, s))
                            addEdge(v0e, edgeH.get(q0).get(q2).get(0));
                        // V1 -> V0 edges [paper ref 11]
                        for (STATE q2 : ba.predInternal(q0, s))
                            if (!ba.isFinal(q0))
                                addEdge(edgeH.get(q2).get(q1).get(0), v0e);
                        v0e = new Player0Vertex<LETTER,STATE>((byte) 2, true, q0, q1, s);
                        v0.add(v0e);
                        // V0 -> V1 edges [paper ref 11]
                        for (STATE q2 : ba.succInternal(q1, s)) {
                            if (!ba.isFinal(q2) && edgeH.get(q0).get(q2).size() > 1)
                                addEdge(v0e, edgeH.get(q0).get(q2).get(1));
                            else addEdge(v0e, edgeH.get(q0).get(q2).get(0));
                        }
                        // V1 -> V0 edges [paper ref 11]
                        for (STATE q2 : ba.predInternal(q0, s)) {
                            if (edgeH.get(q2).get(q1).size() > 1)
                                addEdge(edgeH.get(q2).get(q1).get(1), v0e);
                            if (ba.isFinal(q0))
                                addEdge(edgeH.get(q2).get(q1).get(0), v0e);
                        }
                    }
                }
            }
            if (!m_UltiServ.continueProcessing()) {
                s_Logger.debug("Stopped in generateGameGraph/calculating v0 und v1");
                throw new OperationCanceledException();
            }
        }
        infinity++; // global infinity = (# of pr==1 nodes) + 1
        if (s_Logger.isDebugEnabled()) {
            s_Logger.debug("Infinity is " + infinity);
            s_Logger.debug("Number of vertices in game graph: "
                    + (v0.size() + v1.size()));
            s_Logger.debug("Number of vertices in v0: " + v0.size());
            s_Logger.debug("Number of vertices in v1: " + v1.size());
            int edges = 0;
            for (HashSet<Vertex<LETTER,STATE>> hs : e.values()) {
                edges += hs.size();
            }
            s_Logger.debug("Number of edges in game graph: " + edges);
        }
    }

    /**
     * Adds an edge to the edge set and the inverse edge set.
     * 
     * @param src
     *            the edge source
     * @param dest
     *            the edge destination
     */
    private void addEdge(Vertex<LETTER,STATE> src, Vertex<LETTER, STATE> dest) {
        if (!e.containsKey(src)) e.put(src, new HashSet<Vertex<LETTER,STATE>>());
        e.get(src).add(dest);
        if (!eI.containsKey(dest)) eI.put(dest, new HashSet<Vertex<LETTER,STATE>>());
        eI.get(dest).add(src);
    }

    /**
     * Efficient implementation of the lifting algorithm. (see figure 2 in the
     * paper.
     * 
     * 
     */
    /**
     * Efficient implementation of the lifting algorithm extended with an SCC
     * approach. (see figure 2 in the paper).
     * 
     * @param l_inf
     *            local infinity of the SCC, set to infinity if used w/o SCCs
     * @param scc
     *            vertices the SCC for which we compute the progress measures
     *            are computed, null if used w/o SCC optimization
     * @throws OperationCanceledException
     */
    private void efficientLiftingAlgorithm(int l_inf,
            Set<Vertex<LETTER,STATE>> scc)
            throws OperationCanceledException {
        // init STATE in all vertices and create the working list
        Stack<Vertex<LETTER,STATE>> wL = new Stack<Vertex<LETTER, STATE>>();
        if(useSCCs) {
          HashSet<Vertex<LETTER,STATE>> notDeadEnd = new HashSet<Vertex<LETTER, STATE>>();
          for (Vertex<LETTER,STATE> v : scc) {
              if (v.getPM(scc,infinity) != update(v, l_inf, scc)) {
                  if (!e.containsKey(v)) wL.push(v);
                  else notDeadEnd.add(v);
                  v.setInWL(true);
              }
              v.setC(cnt(v, l_inf, scc));
          }
          wL.addAll(notDeadEnd);
        } else {
            HashSet<Vertex<LETTER,STATE>> notDeadEnd = new HashSet<Vertex<LETTER, STATE>>();
            for (Player0Vertex<LETTER,STATE> v : v0) {
                if (v.getPM(scc,infinity) != update(v, l_inf, scc)) {
                    if (!e.containsKey(v)) wL.push(v);
                    else notDeadEnd.add(v);
                    v.setInWL(true);
                }
                if (e.containsKey(v)) v.setC(e.get(v).size());
            }
            for (Player1Vertex<LETTER,STATE> v : v1) {
                if (v.getPM(scc,infinity) != update(v, l_inf, scc)) {
                    if (!e.containsKey(v)) wL.push(v);
                    else notDeadEnd.add(v);
                    v.setInWL(true);
                }
                if (e.containsKey(v)) v.setC(e.get(v).size());
            }
            wL.addAll(notDeadEnd);
        }
        while (!wL.isEmpty()) {
            Vertex<LETTER,STATE> v = wL.pop();
            v.setInWL(false);
            int t = v.getPM(scc,infinity);
            v.setBEff(bestNghbMS(v, l_inf, scc));
            v.setC(cnt(v, l_inf, scc));
            v.setPM(incr(v.getPriority(), v.getBEff(), l_inf));
            if (!eI.containsKey(v)) continue;
            for (Vertex<LETTER,STATE> w : eI.get(v)) {
                if(useSCCs && !scc.contains(w)) continue;
                // for each predecessor w of v
                if (!w.isInWL()
                        && decrVec(w.getPriority(), v.getPM(scc,infinity), l_inf) > w.getBEff()) {
                    /* w in L && <p(v)>_w > B(w) means: for each predecessor w
                     * of v which is not in L */
                    if (w.isInV0()
                            && decrVec(w.getPriority(), t, l_inf) == w.getBEff()) {
                        /* w in v0 && <l>_w==w.getB() */
                        if (w.getC() == 1) {
                            wL.push(w);
                            w.setInWL(true);
                        }
                        if (w.getC() > 1) w.setC(w.getC() - 1);
                    } else if (w.isInV1()) {
                        wL.push(w);
                        w.setInWL(true);
                    }
                }
            }
            if (!m_UltiServ.continueProcessing()) {
                s_Logger.debug("Stopped in efficientLiftingAlgorithm");
                throw new OperationCanceledException();
            }
        }
    }

    /**
     * Calculates the number of successors u of v with <rho(u)>_v ==
     * bestNghb(v).
     * 
     * @param v
     *            the vertex for which the calculation should be done.
     * @param l_inf
     *            local infinity of SCC, if SCCs not used, param set to infinity
     * @return the number of successors u of v for which the condition
     *         <p(u)>
     *         _v == bestNghb(v) holds.
     */
    private int cnt(Vertex<LETTER,STATE> v, int l_inf, Set<Vertex<LETTER, STATE>> scc) {
        if (!e.containsKey(v)) return 0; // there are no successors
        int cnt = 0;
        for (Vertex<LETTER,STATE> u : e.get(v))
            // for each successor u of v
            if (decrVec(v.getPriority(), u.getPM(scc,infinity), l_inf) == v.getBEff())
                cnt++; /* <rho(u)>_v == bestNghb(v) */
        return cnt;
    }

    /**
     * Update method as described in the paper (paper shortcut 23).
     * 
     * @param v
     *            Vertex v
     * @param l_inf
     *            local infinity of SCC, if SCCs not used, param set to infinity
     * @param scc 
     *            the SCC of v, null if used w/o SCC optimization
     * @return progress measure
     */
    private int update(Vertex<LETTER,STATE> v, int l_inf, Set<Vertex<LETTER, STATE>> scc) {
        return incr(v.getPriority(), bestNghbMS(v, l_inf, scc), l_inf);
    }

    /**
     * Decreases a given vector to position i.
     * 
     * @param i
     *            the position
     * @param x
     *            progress measure x
     * @return new vector
     */
    private int decrVec(byte i, int x, int l_inf) {
        if (x >= l_inf) return infinity;
        switch (i) {
            case 0: return 0;
            case 1:
            case 2: return x;
            default:
                throw new IllegalArgumentException("i out of range: " + i);
        }
    }

    /**
     * Best neighbor method as described in the paper (paper shortcut 22).
     * 
     * @param v
     *            the vertex to calculate best neighbour for
     * @param l_inf
     *            local infinity of SCC, if SCCs not used, param set to infinity
     * @param scc
     *            the SCC of v, null if used w/o SCC optimization
     * @return progress measure
     */
    private int bestNghbMS(Vertex<LETTER,STATE> v, int l_inf, Set<Vertex<LETTER, STATE>> scc) {
        if (!e.containsKey(v)) return infinity; // there are no successors
        if (v.isInV0()) {
            int min = infinity;
            for (Vertex<LETTER,STATE> w : e.get(v)) {
                if (w.getPM(scc,infinity) < min) {
                	min = w.getPM(scc,infinity);
                }
            }
            return decrVec(v.getPriority(), min, l_inf);
        } else {
            int max = 0;
            for (Vertex<LETTER,STATE> w : e.get(v)) {
            	if (w.getPM(scc,infinity) > max) {
            		max = w.getPM(scc,infinity);
            	}
            }
            return decrVec(v.getPriority(), max, l_inf);
        }
    }

    /**
     * Increase method as described in the paper [paper ref 21].
     * 
     * @param priority
     *            progress measure
     * @param x
     *            the x parameter as in the paper [paper ref 21]
     * @param l_inf
     *            local infinity of SCC, if SCCs not used, param set to infinity
     * @return new progress measure
     */
    private int incr(byte priority, int x, int l_inf) {
        if (x >= l_inf) return infinity;
        switch (priority) {
            case 0:
            case 2: return decrVec(priority, x, l_inf);
            case 1: return x + 1; // next min in M_G^inf : y >_i x
            default:
                throw new IllegalArgumentException("priority out of range: "
                        + priority);
        }
    }

    /**
     * Generate a Buchi automaton from the given GameGraph.
     * 
     * @param gg
     *            the GameGraph on which the algorithm should be applied
     * @return a Buchi automaton with reduced state space
     * @throws OperationCanceledException
     */
    private void generateBuchiAutomaton(INestedWordAutomaton<LETTER,STATE> m_Operand)
            throws OperationCanceledException {
        // determine which states to merge
        ArrayList<STATE> states = new ArrayList<STATE>();
        states.addAll(m_Operand.getStates());
        boolean[][] table = new boolean[states.size()][states.size()];
        for (Player1Vertex<LETTER,STATE> v : v1) {
            // all the states we need are in V1...
            if ((m_Operand.isFinal(v.getQ0()) && m_Operand.isFinal(v.getQ1()))
                    ^ v.isB() ^ m_Operand.isFinal(v.getQ0())) {
                // skip all elements that not fulfill:
                // letting b=1 if q0 in F and q1 not in F, and b=0 else
                continue;
            }
            if (v.getPM(null,infinity) < infinity) {
                table[states.indexOf(v.getQ0())][states.indexOf(v.getQ1())] = true;
            }
        }

        if (!m_UltiServ.continueProcessing()) {
            s_Logger.debug("Stopped in generateBuchiAutomaton/table filled");
            throw new OperationCanceledException();
        }

        // merge states
        boolean[] marker = new boolean[states.size()];
        Set<STATE> temp = new HashSet<STATE>();
        HashMap<STATE,STATE> oldSNames2newSNames = new HashMap<STATE,STATE>();
        @SuppressWarnings("unchecked")
        StateFactory<STATE> snf = (StateFactory<STATE>) new StringFactory();
        result = new NestedWordAutomaton<LETTER,STATE>(m_Operand.getInternalAlphabet(),
                null, null, snf);
        for (int i = 0; i < states.size(); i++) {
            if (marker[i]) continue;
            temp.clear();
            temp.add(states.get(i));
            marker[i] = true;
            boolean isFinal = m_Operand.isFinal(states.get(i));
            boolean isInitial = m_Operand.isInitial(states.get(i));
            for (int j = i; j < states.size(); j++) {
                if (table[i][j] && table[j][i] && !marker[j]) {
                    temp.add(states.get(j));
                    marker[j] = true;
                    if (m_Operand.isFinal(states.get(j))) isFinal = true;
                    if (m_Operand.isInitial(states.get(j))) isInitial = true;
                }
            }
            STATE minimizedStateName = snf.minimize(temp);
            for (STATE c : temp) oldSNames2newSNames.put(c, minimizedStateName);
            result.addState(isInitial, isFinal, minimizedStateName);
            marker[i] = true;
        }

        if (!m_UltiServ.continueProcessing()) {
            s_Logger.debug("Stopped in generateBuchiAutomaton/states added to result BA");
            throw new OperationCanceledException();
        }

        // add edges
        for (STATE c : m_Operand.getStates())
            for (LETTER s : m_Operand.getInternalAlphabet())
                for (STATE succ : m_Operand.succInternal(c, s)) {
                    STATE newPred = oldSNames2newSNames.get(c);
                    STATE newSucc = oldSNames2newSNames.get(succ);
                    result.addInternalTransition(newPred, s, newSucc);
                }
    }

    /**
     * Helper method to clear memory, if winning strategy was calculated. This
     * is meant to be done manually after the calculation, because the order of
     * the methods can vary!
     */
    private void clear() {
        this.e.clear();
        this.eI.clear();
        this.v0.clear();
        System.gc();
    }

    /**
     * Offers a method to compute the strongly connected components (SCCs) of
     * the game graph.
     * Implementation of Tarjan SCC algorithm. 
     * {@link http://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm}
     * @author heizmann@informatik.uni-freiburg.de
     */
    private class SccComputation {
    	/**
    	 * Number of vertices that have been processed so far.
    	 */
    	int m_Index = 0;
    	/**
    	 * Vertices that have not yet been assigned to any SCC.
    	 */
    	Stack<Vertex<LETTER,STATE>> m_NoScc = 
    			new Stack<Vertex<LETTER,STATE>>();
    	
    	/**
    	 * Assigns to each vertex v the number of vertices that have been
    	 * processed before in this algorithm. This number is called the index
    	 * of v.
    	 */
    	Map<Vertex<LETTER,STATE>,Integer> m_Indices = 
    			new IdentityHashMap<Vertex<LETTER,STATE>,Integer>();

    	Map<Vertex<LETTER,STATE>,Integer> m_LowLinks = 
    			new IdentityHashMap<Vertex<LETTER,STATE>,Integer>();
    	List<DelayedSimulation<LETTER,STATE>.SCC> m_SCCs = 
    			new LinkedList<DelayedSimulation<LETTER,STATE>.SCC>();
    	
        public SccComputation() {
            for (Player0Vertex<LETTER,STATE> v : v0) {
                if (!m_Indices.containsKey(v)) {
                    strongconnect(v);
                }
            }

            for (Player1Vertex<LETTER,STATE> v : v1) {
                if (!m_Indices.containsKey(v)) {
                    strongconnect(v);
                }
            }
            s_Logger.debug("Game graph consists of " + m_SCCs.size() + " SCCs");
        }

        private void strongconnect(Vertex<LETTER,STATE> v) {
            assert (!m_Indices.containsKey(v));
            assert (!m_LowLinks.containsKey(v));
            m_Indices.put(v, m_Index);
            m_LowLinks.put(v, m_Index);
            m_Index++;
            this.m_NoScc.push(v);

            if(e.containsKey(v)) {
                for (Vertex<LETTER,STATE> w : e.get(v)) {
                    if (!m_Indices.containsKey(w)) {
                        strongconnect(w);
                        int minLowLink = Math.min(m_LowLinks.get(v),
                                m_LowLinks.get(w));
                        m_LowLinks.put(v, minLowLink);
                    } else if (m_NoScc.contains(w)) {
                        int min = Math.min(m_LowLinks.get(v), m_Indices.get(w));
                        m_LowLinks.put(v, min);
                    }
                }
            }
            
            if (m_LowLinks.get(v).equals(m_Indices.get(v))) {
                Vertex<LETTER,STATE> w;
                Set<Vertex<LETTER,STATE>> verticesOfSCC = 
                		new HashSet<Vertex<LETTER,STATE>>();
                int priorityOneVerticesOfScc = 0;
                do {
                    w = m_NoScc.pop();
                    verticesOfSCC.add(w);
                    if (w.getPriority() == 1) {
                    	priorityOneVerticesOfScc++;
                    }
  
                } while (v != w);
                @SuppressWarnings({ "unchecked", "rawtypes" })
    			DelayedSimulation<LETTER,STATE>.SCC scc = new DelayedSimulation.SCC(
    								   verticesOfSCC, priorityOneVerticesOfScc);
                m_SCCs.add(scc);
            }
        }
        
        
        /**
         * @return List of SCCs of the game graph in reverse topological order.
         * (This means: If scc1 occurs in this list before scc2 then ss2 is not
         * reachable from scc1).
         */
        public List<SCC> getSCCs() {
        	assert(gameGraphPartitionedBySCCs());
        	return m_SCCs;
        }
        
        /**
         * @return true iff the SCCS form a partition of the game graph.
         */
        private boolean gameGraphPartitionedBySCCs() {
        	int verticesInAllSccs = 0;
        	int max = 0;
        	for (SCC scc : m_SCCs) {
        		verticesInAllSccs += scc.getVertices().size();
        	}
        	s_Logger.debug("The biggest SCC has " + max + " vertices.");
        	int verticesInGameGraph = v0.size() + v1.size();
        	boolean sameNumberOfVertices = 
        			(verticesInAllSccs == verticesInGameGraph);
        	return sameNumberOfVertices;
        }
    }
    
    
    /**
     * A strongly connected component (SCC) of a game graph. Stores a set of
     * vertices and the number of all vertices that have priority 1.
     * @author heizmann@informatik.uni-freiburg.de
     *
     */
    class SCC {
    	private final Set<Vertex<LETTER,STATE>> m_Vertices;
        private final int m_SCCsVerticesWithPriorityOne;

        public SCC(Set<Vertex<LETTER,STATE>> vertices, 
        		int priorityOneVerticesOfScc) {
            this.m_Vertices = vertices;
            this.m_SCCsVerticesWithPriorityOne = priorityOneVerticesOfScc;
        }
        
		/**
         * @return all vertices of this SCC
         */
        public Set<Vertex<LETTER,STATE>> getVertices() {
			return m_Vertices;
		}
        
        /**
         * @return number vertices of this SCC that have priority 1.
         */
		private int getSCCsVerticesWithPriorityOne() {
			return m_SCCsVerticesWithPriorityOne;
		}

    }
}