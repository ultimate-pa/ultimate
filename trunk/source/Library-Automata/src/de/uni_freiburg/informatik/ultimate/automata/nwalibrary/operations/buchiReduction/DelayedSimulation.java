/*
 * Copyright (C) 2009-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
/**
 * Buchi automata state space reduction algorithm based on the following paper:
 * "Fair simulation relations, parity games and state space reduction for
 * Buchi automata" - Etessami, Wilke and Schuller.
 * 
 * Algorithm optimized to work using strongly connected components.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Player0Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Player1Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

/**
 * @author Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * @author Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * @date 16.01.2012
 */
public class DelayedSimulation<LETTER,STATE> extends AbstractSimulation<LETTER, STATE> {

    /**
     * Constructor.
     * 
     * @param ba
     *            the input buchi automaton to reduce.
     * @param useSCCs
     *            whether to use strongly connected components
     * @throws OperationCanceledException
     */
    public DelayedSimulation(IUltimateServiceProvider services,
    		INestedWordAutomatonOldApi<LETTER,STATE> ba, 
    		boolean useSCCs, StateFactory<STATE> stateFactory)
            throws OperationCanceledException {
    	super(services, ba, useSCCs, stateFactory);
    }

    /**
     * Generates a GameGraph for a given Buchi automaton.
     * 
     * @param ba
     *            a Buchi automaton <b>without</b> dead ends
     * @throws OperationCanceledException
     */
    protected void generateGameGraph(INestedWordAutomatonOldApi<LETTER,STATE> ba)
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
            if (!m_Services.getProgressMonitorService().continueProcessing()) {
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
            if (!m_Services.getProgressMonitorService().continueProcessing()) {
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
     * Generate a Buchi automaton from the given GameGraph.
     * 
     * @param gg
     *            the GameGraph on which the algorithm should be applied
     * @return a Buchi automaton with reduced state space
     * @throws OperationCanceledException
     */
    protected void generateBuchiAutomaton(INestedWordAutomatonOldApi<LETTER,STATE> m_Operand)
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

        if (!m_Services.getProgressMonitorService().continueProcessing()) {
            s_Logger.debug("Stopped in generateBuchiAutomaton/table filled");
            throw new OperationCanceledException();
        }

        // merge states
        boolean[] marker = new boolean[states.size()];
        Set<STATE> temp = new HashSet<STATE>();
        HashMap<STATE,STATE> oldSNames2newSNames = new HashMap<STATE,STATE>();
        @SuppressWarnings("unchecked")
        StateFactory<STATE> snf = (StateFactory<STATE>) new StringFactory();
        result = new NestedWordAutomaton<LETTER,STATE>(m_Services, m_Operand.getInternalAlphabet(),
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

        if (!m_Services.getProgressMonitorService().continueProcessing()) {
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

}