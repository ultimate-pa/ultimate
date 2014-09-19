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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Player0Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Player1Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap2;

/**
 */
public class DirectSimulation<LETTER,STATE> extends AbstractSimulation<LETTER, STATE> {

    /**
     * Constructor.
     * 
     * @param ba
     *            the input buchi automaton to reduce.
     * @param useSCCs
     *            whether to use strongly connected components
     * @throws OperationCanceledException
     */
    public DirectSimulation(INestedWordAutomatonOldApi<LETTER,STATE> ba, boolean useSCCs, StateFactory<STATE> stateFactory)
            throws OperationCanceledException {
    	super(ba, useSCCs, stateFactory);
    }

    /**
     * Generates a GameGraph for a given DFA
     * 
     * @param ba
     *            a Buchi automaton <b>without</b> dead ends
     * @throws OperationCanceledException
     */
    protected void generateGameGraph(INestedWordAutomatonOldApi<LETTER,STATE> ba)
            throws OperationCanceledException {
    	NestedMap2<STATE, STATE, Player1Vertex<LETTER,STATE>> map1 = new NestedMap2<STATE, STATE, Player1Vertex<LETTER,STATE>>();
        // Calculate v1 [paper ref 10]
        for (STATE q0 : ba.getStates()) {
            for (STATE q1 : ba.getStates()) {
                Player1Vertex<LETTER,STATE> v1e = new Player1Vertex<LETTER, STATE>(
                        (byte) 0, false, q0, q1);
                v1.add(v1e);
                map1.put(q0, q1, v1e);
            }
            if (!NestedWordAutomata.getMonitor().continueProcessing()) {
                s_Logger.debug("Stopped in generateGameGraph/calculating v0 und v1");
                throw new OperationCanceledException();
            }
        }
        // Calculate v0 and edges [paper ref 10, 11, 12]
        for (STATE q0 : ba.getStates()) {
            for (STATE q1 : ba.getStates()) {
            	Set<LETTER> relevantLetters = new HashSet<LETTER>();
            	relevantLetters.addAll(ba.lettersInternalIncoming(q0));
            	relevantLetters.addAll(ba.lettersInternal(q1));
                for (LETTER s : relevantLetters) {
                    Player0Vertex<LETTER,STATE> v0e = new Player0Vertex<LETTER, STATE>(
                            (byte) 0, false, q0, q1, s);
                    v0.add(v0e);
                    // V1 -> V0 edges [paper ref 11]
                    for (STATE pred0 : ba.predInternal(q0, s)) {
                    	//TODO: check conditions
                        if (!ba.isFinal(pred0) || ba.isFinal(q1)) {
                            addEdge(map1.get(pred0, q1), v0e);
                        }
                    }
                    // V0 -> V1 edges [paper ref 11]
                    for (STATE succ1 : ba.succInternal(q1, s)) {
                    	//TODO: check conditions
                        if (!ba.isFinal(q0) || ba.isFinal(succ1)) {
                            addEdge(v0e, map1.get(q0, succ1));
                        }
                    }
                }
            }
            if (!NestedWordAutomata.getMonitor().continueProcessing()) {
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
    	UnionFind<STATE> uf = new UnionFind<>();
    	for (STATE state : m_Operand.getStates()) {
    		uf.makeEquivalenceClass(state);
    	}
    	HashRelation<STATE, STATE> similarStates = new HashRelation<STATE, STATE>();
        for (Player1Vertex<LETTER,STATE> v : v1) {
            // all the states we need are in V1...
            if (v.getPM(null,infinity) < infinity) {
            	STATE state1 = v.getQ0();
            	STATE state2 = v.getQ1();
            	similarStates.addPair(state1, state2);
            	
            }
        }
        // merge if bisimilar
        for (STATE state1 : similarStates.getDomain()) {
        	for (STATE state2 : similarStates.getImage(state1)) {
        		if (similarStates.containsPair(state2, state1)) {
        			uf.union(state1, state2);	
        		}
        	}
        }
        

        if (!NestedWordAutomata.getMonitor().continueProcessing()) {
            s_Logger.debug("Stopped in generateBuchiAutomaton/table filled");
            throw new OperationCanceledException();
        }

        // merge states
        result = new NestedWordAutomaton<LETTER,STATE>(m_Operand.getInternalAlphabet(),
                null, null, m_StateFactory);
        Set<STATE> representativesOfInitials = new HashSet<STATE>();
        for (STATE initial : m_Operand.getInitialStates()) {
        	representativesOfInitials.add(uf.find(initial));
        }
        
        Map<STATE,STATE> input2result = new HashMap<STATE,STATE>(m_Operand.size());
        for (STATE representative : uf.getAllRepresentatives()) {
        	boolean isInitial = representativesOfInitials.contains(representative);
        	boolean isFinal = m_Operand.isFinal(representative);
        	Set<STATE> eqClass = uf.getEquivalenceClassMembers(representative);
        	STATE resultState = m_StateFactory.minimize(eqClass);
        	result.addState(isInitial, isFinal, resultState);
        	for (STATE eqClassMember : eqClass) {
        		input2result.put(eqClassMember, resultState);
        	}
        }
        
        for (STATE state : uf.getAllRepresentatives()) {
        	STATE pred = input2result.get(state);
        	for (OutgoingInternalTransition<LETTER, STATE> outTrans : m_Operand.internalSuccessors(state)) {
        		STATE succ = input2result.get(outTrans.getSucc());
        		result.addInternalTransition(pred, outTrans.getLetter(), succ);
        	}
        }
        
        if (!NestedWordAutomata.getMonitor().continueProcessing()) {
            s_Logger.debug("Stopped in generateBuchiAutomaton/states added to result BA");
            throw new OperationCanceledException();
        }

    }

}