/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2009-2016 University of Freiburg
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
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.fair;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.GameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Player0Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Player1Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;

/**
 * Doc comes later.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 * @param <STATE>
 */
public final class FairGameGraph<LETTER, STATE> extends GameGraph<LETTER, STATE> {
	
	private INestedWordAutomatonOldApi<LETTER, STATE> buechi;

	private int globalInfinity = 0;

	public FairGameGraph(IUltimateServiceProvider services, INestedWordAutomatonOldApi<LETTER, STATE> thatBuechi) {
		super(services);
		buechi = thatBuechi;
		generateGameGraphFromBuechi();
	}

	public int getGlobalInfinity() {
		return globalInfinity;
	}
	
	@Override
	protected byte calculatePriority(STATE leftState, STATE rightState) {
		if (buechi.isFinal(rightState)) {
			return (byte) 0;
		} else if (buechi.isFinal(leftState)) {
			return (byte) 1;
		} else {
			return (byte) 2;
		}
	}
	
	@Override
	protected void generateGameGraphFromBuechi() {
		// Generate states
		for (STATE leftState : buechi.getStates()) {
			for (STATE rightState : buechi.getStates()) {
				// Generate V_1 states
				byte priority = calculatePriority(leftState, rightState);
				if (priority == (byte) 1) {
					globalInfinity++;
				}
				Player1Vertex<LETTER, STATE> v1e =
						new Player1Vertex<LETTER, STATE>(priority, false, leftState, rightState);
				addPlayer1State(v1e);
				
				// Generate V_0 states
				for (LETTER letter : buechi.lettersInternalIncoming(leftState)) {
					Player0Vertex<LETTER, STATE> v0e =
							new Player0Vertex<LETTER, STATE>((byte) 2, false, leftState, rightState, letter);
					addPlayer0State(v0e);
				}
			}
		}

		globalInfinity++;

		// Generate edges
		for (STATE edgeDestination : buechi.getStates()) {
			for (IncomingInternalTransition<LETTER, STATE> transition : buechi.internalPredecessors(edgeDestination)) {
				for (STATE fixState : buechi.getStates()) {
					// Duplicator edges V_0 -> V_1
					Vertex<LETTER, STATE> origin = getPlayer0State(fixState, transition.getPred(), transition.getLetter());
					Vertex<LETTER, STATE> destination = getPlayer1State(fixState, edgeDestination);
					if (origin != null && destination != null) {
						addEdge(origin, destination);
					}

					// Spoiler edges V_1 -> V_0
					origin = getPlayer1State(transition.getPred(), fixState);
					destination = getPlayer0State(edgeDestination, fixState, transition.getLetter());
					if (origin != null && destination != null) {
						addEdge(origin, destination);
					}
					// TODO Can Null-Pointer occur? Can it link trivial edges
					// like V_0 -> V_1 where origin has no predecessors?
					// Can we generate edges at the same time we generate
					// states?
				}
			}
		}
	}
	
	@Override
	protected NestedWordAutomaton<LETTER, STATE> generateBuchiAutomatonFromGraph() {
		// TODO Currently returns a copy of the buechi automata.
		StateFactory<STATE> snf = (StateFactory<STATE>) new StringFactory();
		NestedWordAutomaton<LETTER, STATE> result = new NestedWordAutomaton<LETTER, STATE>(m_Services,
				buechi.getInternalAlphabet(), null, null, snf);

		// Add states
		for (STATE state : buechi.getStates()) {
			result.addState(buechi.isInitial(state), buechi.isFinal(state), state);
		}

		// Add edges
		for (STATE origin : buechi.getStates()) {
			for (OutgoingInternalTransition<LETTER, STATE> edge : buechi.internalSuccessors(origin)) {
				if (edge != null) {
					result.addInternalTransition(origin, edge.getLetter(), edge.getSucc());
				}
			}
		}
		return result;
	}
	
	@Override
	public String toString() {
		StringBuilder result = new StringBuilder();
		String lineSeparator = System.lineSeparator();
		// Header
		result.append("FairGameGraph fgg = (");
		
		// States
		result.append(lineSeparator + "\tplayer1Vertices = {");
		for (Player1Vertex<LETTER, STATE> state : getPlayer1States()) {
			result.append(lineSeparator + "\t\t<(" + state.getQ0()
				+ ", " + state.getQ1() + "), p:" + state.getPriority() + ">");
		}
		result.append(lineSeparator + "\t},");
		result.append(lineSeparator + "\tplayer0Vertices = {");
		for (Player0Vertex<LETTER, STATE> state : getPlayer0States()) {
			result.append(lineSeparator + "\t\t<(" + state.getQ0()
				+ ", " + state.getQ1() + ", " + state.getLetter()
				+ "), p:" + state.getPriority() + ">");
		}
		result.append(lineSeparator + "\t},");
		
		// Edges
		result.append(lineSeparator + "\ttransitions = {");
		for (Vertex<LETTER, STATE> state : getNonDeadEndStates()) {
			for (Vertex<LETTER, STATE> successor : getSuccessors(state)) {
				result.append(lineSeparator + "\t\t(" + state.getQ0() + ", " + state.getQ1());
				if (state instanceof Player0Vertex) {
					Player0Vertex<LETTER, STATE> stateAsPlayer0 = (Player0Vertex<LETTER, STATE>) state;
					result.append(", " + stateAsPlayer0.getLetter());
				}
				result.append(")\t--> (" + successor.getQ0() + ", " + successor.getQ1());
				if (successor instanceof Player0Vertex) {
					Player0Vertex<LETTER, STATE> successorAsPlayer0 = (Player0Vertex<LETTER, STATE>) successor;
					result.append(", " + successorAsPlayer0.getLetter());
				}
				result.append(")");
			}
		}
		result.append(lineSeparator + "\t}");
		
		// Footer
		result.append(lineSeparator + ");");
		
		return result.toString();
	}
}
