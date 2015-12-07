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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.SpoilerVertex;
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
public final class FairGameGraph<LETTER, STATE> extends AGameGraph<LETTER, STATE> {
	
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Buechi;
	
	public FairGameGraph(final IUltimateServiceProvider services,
			final INestedWordAutomatonOldApi<LETTER, STATE> buechi) {
		super(services);
		m_Buechi = buechi;
		generateGameGraphFromBuechi();
	}
	
	@Override
	public String toString() {
		StringBuilder result = new StringBuilder();
		String lineSeparator = System.lineSeparator();
		// Header
		result.append("FairGameGraph fgg = (");
		
		// States
		result.append(lineSeparator + "\tSpoilerVertices = {");
		for (SpoilerVertex<LETTER, STATE> vertex : getSpoilerVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0()
				+ ", " + vertex.getQ1() + "), p:" + vertex.getPriority() + ">");
		}
		result.append(lineSeparator + "\t},");
		result.append(lineSeparator + "\tDuplicatorVertices = {");
		for (DuplicatorVertex<LETTER, STATE> vertex : getDuplicatorVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0()
				+ ", " + vertex.getQ1() + ", " + vertex.getLetter()
				+ "), p:" + vertex.getPriority() + ">");
		}
		result.append(lineSeparator + "\t},");
		
		// Edges
		result.append(lineSeparator + "\tedges = {");
		for (Vertex<LETTER, STATE> vertex : getNonDeadEndVertices()) {
			for (Vertex<LETTER, STATE> succ : getSuccessors(vertex)) {
				result.append(lineSeparator + "\t\t(" + vertex.getQ0() + ", " + vertex.getQ1());
				if (vertex instanceof DuplicatorVertex) {
					DuplicatorVertex<LETTER, STATE> vertexAsDuplicatorVertex = (DuplicatorVertex<LETTER, STATE>) vertex;
					result.append(", " + vertexAsDuplicatorVertex.getLetter());
				}
				result.append(")\t--> (" + succ.getQ0() + ", " + succ.getQ1());
				if (succ instanceof DuplicatorVertex) {
					DuplicatorVertex<LETTER, STATE> vertexAsDuplicatorVertex = (DuplicatorVertex<LETTER, STATE>) succ;
					result.append(", " + vertexAsDuplicatorVertex.getLetter());
				}
				result.append(")");
			}
		}
		result.append(lineSeparator + "\t}");
		
		// Footer
		result.append(lineSeparator + ");");
		
		return result.toString();
	}
	
	private int calculatePriority(final STATE leftState, final STATE rightState) {
		if (m_Buechi.isFinal(rightState)) {
			return 0;
		} else if (m_Buechi.isFinal(leftState)) {
			return 1;
		} else {
			return 2;
		}
	}
	
	@Override
	protected NestedWordAutomaton<LETTER, STATE> generateBuchiAutomatonFromGraph() {
		// TODO Currently returns a copy of the buechi automata.
		@SuppressWarnings("unchecked")
		StateFactory<STATE> snf = (StateFactory<STATE>) new StringFactory();
		NestedWordAutomaton<LETTER, STATE> result = new NestedWordAutomaton<LETTER, STATE>(getServiceProvider(),
				m_Buechi.getInternalAlphabet(), null, null, snf);

		// Add states
		for (STATE state : m_Buechi.getStates()) {
			result.addState(m_Buechi.isInitial(state), m_Buechi.isFinal(state), state);
		}

		// Add edges
		for (STATE src : m_Buechi.getStates()) {
			for (OutgoingInternalTransition<LETTER, STATE> trans : m_Buechi.internalSuccessors(src)) {
				if (trans != null) {
					result.addInternalTransition(src, trans.getLetter(), trans.getSucc());
				}
			}
		}
		return result;
	}
	
	@Override
	protected void generateGameGraphFromBuechi() {
		// Generate states
		for (STATE leftState : m_Buechi.getStates()) {
			for (STATE rightState : m_Buechi.getStates()) {
				// Generate Spoiler vertices
				int priority = calculatePriority(leftState, rightState);
				if (priority == 1) {
					increaseGlobalInfinity();
				}
				SpoilerVertex<LETTER, STATE> spoilerVertex =
						new SpoilerVertex<LETTER, STATE>(priority, false, leftState, rightState);
				addSpoilerVertex(spoilerVertex);
				
				// Generate Duplicator vertices
				for (LETTER letter : m_Buechi.lettersInternalIncoming(leftState)) {
					DuplicatorVertex<LETTER, STATE> duplicatorVertex =
							new DuplicatorVertex<LETTER, STATE>(2, false, leftState, rightState, letter);
					addDuplicatorVertex(duplicatorVertex);
				}
			}
		}

		increaseGlobalInfinity();

		// Generate edges
		for (STATE edgeDest : m_Buechi.getStates()) {
			for (IncomingInternalTransition<LETTER, STATE> trans : m_Buechi.internalPredecessors(edgeDest)) {
				for (STATE fixState : m_Buechi.getStates()) {
					// Duplicator edges
					Vertex<LETTER, STATE> src = getDuplicatorVertex(fixState, trans.getPred(), trans.getLetter(), false);
					Vertex<LETTER, STATE> dest = getSpoilerVertex(fixState, edgeDest, false);
					if (src != null && dest != null) {
						addEdge(src, dest);
					}

					// Spoiler edges
					src = getSpoilerVertex(trans.getPred(), fixState, false);
					dest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), false);
					if (src != null && dest != null) {
						addEdge(src, dest);
					}
					// TODO Can Null-Pointer occur? Can it link trivial edges
					// like V_0 -> V_1 where origin has no predecessors?
					// TODO Can we generate edges at the same time we generate states?
				}
			}
		}
	}
}
