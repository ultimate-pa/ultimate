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

import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.GameGraphChangeType;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.GameGraphChanges;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.relation.Triple;

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
	
	/**
	 * True for added, false for removed.
	 */
	private final NestedMap3<STATE, LETTER, STATE, GameGraphChangeType> m_ChangedBuechiTransitionsInverse;
	
	public FairGameGraph(final IUltimateServiceProvider services,
			final INestedWordAutomatonOldApi<LETTER, STATE> buechi) {
		super(services);
		
		m_Buechi = buechi;
		m_ChangedBuechiTransitionsInverse = new NestedMap3<STATE, LETTER, STATE, GameGraphChangeType>();
		
		generateGameGraphFromBuechi();
	}
	
	@Override
	public String toString() {
		StringBuilder result = new StringBuilder();
		String lineSeparator = System.lineSeparator();
		// Header
		result.append("FairGameGraph fgg = (");
		
		// Vertices
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
	
	@Override
	public void undoChanges(final GameGraphChanges<LETTER, STATE> changes) {
		super.undoChanges(changes);
		
		if (changes == null) {
			return;
		}
		
		if (changes instanceof FairGameGraphChanges) {
			FairGameGraphChanges<LETTER, STATE> fairChanges =
					(FairGameGraphChanges<LETTER, STATE>) changes;
			// Undo buechi transition changes
			NestedMap3<STATE, LETTER, STATE,
				GameGraphChangeType> changedTransitions =
				fairChanges.getChangedBuechiTransitions();
			for (STATE changedKey : changedTransitions.keySet()) {
				for (Triple<LETTER, STATE,
						GameGraphChangeType> changedTrans :
							changedTransitions.get(changedKey).entrySet()) {
					STATE src = changedKey;
					LETTER a = changedTrans.getFirst();
					STATE dest = changedTrans.getSecond();
					if (changedTrans.getThird().equals(
							GameGraphChangeType.ADDITION)
							|| changedTrans.getThird().equals(
									GameGraphChangeType.REMOVAL)) {
						m_ChangedBuechiTransitionsInverse.put(src, a,
								dest, GameGraphChangeType.NO_CHANGE);
					}
				}
			}
		}
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
	
	private FairGameGraphChanges<LETTER, STATE> equalizeBuechiStatesOneDir(
			final STATE stateToAlign, final STATE stateToAlignTo) {
		Set<STATE> states = m_Buechi.getStates();
		if (stateToAlignTo == null || stateToAlign == null
				|| !states.contains(stateToAlignTo)
				|| !states.contains(stateToAlign)
				|| stateToAlignTo == stateToAlign) {
			throw new IllegalArgumentException("Arguments must exist in the"
					+ " automaton, be different and not null.");
		}
		
		FairGameGraphChanges<LETTER, STATE> changes =
				new FairGameGraphChanges<LETTER, STATE>();
		boolean madeAChange = false;
		
		// Work successors of stateToAlignTo
		for (OutgoingInternalTransition<LETTER, STATE> trans
				: m_Buechi.internalSuccessors(stateToAlignTo)) {
			boolean transCovered = false;
			for (OutgoingInternalTransition<LETTER, STATE> coveringTrans
					: m_Buechi.internalSuccessors(stateToAlign, trans.getLetter())) {
				if (coveringTrans.getSucc().equals(trans.getSucc())) {
					transCovered = true;
					break;
				}
			}
			if (!transCovered) {
				FairGameGraphChanges<LETTER, STATE> currentChange =
						addBuechiTransition(stateToAlign, trans.getLetter(),
								trans.getSucc());
				if (currentChange != null) {
					changes.merge(currentChange, true);
					madeAChange = true;
				}
			}
		}
		// Work predecessors of stateToAlignTo
		for (IncomingInternalTransition<LETTER, STATE> trans
				: m_Buechi.internalPredecessors(stateToAlignTo)) {
			boolean transCovered = false;
			for (IncomingInternalTransition<LETTER, STATE> coveringTrans
					: m_Buechi.internalPredecessors(trans.getLetter(), stateToAlign)) {
				if (coveringTrans.getPred().equals(trans.getPred())) {
					transCovered = true;
					break;
				}
			}
			if (!transCovered) {
				FairGameGraphChanges<LETTER, STATE> currentChange =
						addBuechiTransition(trans.getPred(), trans.getLetter(),
								stateToAlign);
				if (currentChange != null) {
					changes.merge(currentChange, true);
					madeAChange = true;
				}
			}
		}
		
		if (madeAChange) {
			return changes;
		} else {
			return null;
		}
	}
	
	/**
	 * Assuming given transition does not exist already
	 * @param src
	 * @param a
	 * @param dest
	 * @return
	 */
	protected FairGameGraphChanges<LETTER, STATE> addBuechiTransition(
			final STATE src, final LETTER a, final STATE dest) {
		Set<STATE> states = m_Buechi.getStates();
		if (src == null || dest == null
				|| !states.contains(src) || !states.contains(dest)) {
			throw new IllegalArgumentException("Arguments must exist in the"
					+ " automaton and not be null.");
		}
		GameGraphChangeType wasChangedBefore = m_ChangedBuechiTransitionsInverse.get(dest, a, src);
		if (wasChangedBefore != null && wasChangedBefore.equals(GameGraphChangeType.ADDITION)) {
			// Transition was already added previously.
			return null;
		}
		
		// Check if letter is a new incoming letter for destination
		boolean isLetterNew = true;
		Map<STATE, GameGraphChangeType> changedPreds = m_ChangedBuechiTransitionsInverse.get(dest, a);
		// First iterate over original transitions
		Iterator<STATE> iter = m_Buechi.predInternal(dest, a).iterator();
		while (iter.hasNext()) {
			STATE pred = iter.next();
			// Ignore transition if it was removed before
			if (changedPreds != null) {
				GameGraphChangeType change = changedPreds.get(pred);
				if (change != null && change.equals(GameGraphChangeType.REMOVAL)) {
					continue;
				}
			}
			// Found a valid transition with given letter
			isLetterNew = false;
			break;
		}
		// Second iterate over possible added transitions
		if (isLetterNew && changedPreds != null) {
			for (Entry<STATE, GameGraphChangeType> changeEntry : changedPreds.entrySet()) {
				if (changeEntry.getValue() != null
						&& changeEntry.getValue().equals(GameGraphChangeType.ADDITION)) {
					// Found a valid added transition with given letter
					isLetterNew = false;
					break;
				}
			}
		}
		
		FairGameGraphChanges<LETTER, STATE> changes =
				new FairGameGraphChanges<LETTER, STATE>();
		
		// Generate new edges and some missing vertices
		for (STATE fixState : states) {
			/*
			 *  If letter is new it now generates some new Duplicator vertices
			 *  If 'a' was new for q2: (q2, x, a) gets generated
			 */
			if (isLetterNew) {
				STATE rightState = fixState;
				// Continue if that state already exists or was generated before
				if (getDuplicatorVertex(dest, rightState, a, false) != null) {
					continue;
				}
				DuplicatorVertex<LETTER, STATE> generatedVertex =
						new DuplicatorVertex<LETTER, STATE>(2, false, dest, rightState, a);
				addDuplicatorVertex(generatedVertex);
				// Remember addition
				changes.addedVertex(generatedVertex);
				
				/* 
				 * Generate left edges for newly generated vertices.
				 * 
				 * Newly generated vertices need their left edges that would be there
				 * if they were not be obsolete in the previous graph.
				 * Now they are not obsolete anymore and need to be generated.
				 * 
				 * It is very important that the right state does not give a successor
				 * transition that was added in previous usages of the add-function
				 * or language may change.
				 */
				for (OutgoingInternalTransition<LETTER, STATE> succTrans :
					m_Buechi.internalSuccessors(generatedVertex.getQ1(),
							generatedVertex.getLetter())) {
					/*
					 * Duplicator edges.
					 * If 'a' was new for q2: (q2, x, a) gets generated
					 * and (q2, x, a) -> (q2, succ(x, a)) needs also to be generated.
					 */
					Vertex<LETTER, STATE> edgeDest = getSpoilerVertex(
							generatedVertex.getQ0(), succTrans.getSucc(), false);
					if (src != null && dest != null) {
						addEdge(generatedVertex, edgeDest);
						// Remember addition
						changes.addedEdge(generatedVertex, edgeDest);
					}
					/*
					 * Spoiler edges.
					 * Also (pre(q2, a), x) -> (q2, x, a) needs to be generated but
					 * it gets already covered by the next statement.
					 */
				}
			}
						
			// Generate new edges
			
			// Addition of edges must only be made to vertices of Spoiler
			// Spoiler edges q1 -a-> q2 : (q1, x) -> (q2, x, a)
			Vertex<LETTER, STATE> edgeSrc = getSpoilerVertex(src, fixState, false);
			Vertex<LETTER, STATE> edgeDest = getDuplicatorVertex(dest, fixState, a, false);
			if (src != null && dest != null) {
				addEdge(edgeSrc, edgeDest);
				// Remember addition
				changes.addedEdge(edgeSrc, edgeDest);
			}
		}
		
		// Update set of changes
		m_ChangedBuechiTransitionsInverse.put(dest, a, src, GameGraphChangeType.ADDITION);
		changes.addedBuechiTransition(src, a, dest);
		
		return changes;
	}
	
	protected FairGameGraphChanges<LETTER, STATE> equalizeBuechiStates(
			final STATE firstState, final STATE secondState) {
		Set<STATE> states = m_Buechi.getStates();
		if (firstState == null || secondState == null
				|| !states.contains(firstState) || !states.contains(secondState)
				|| firstState == secondState) {
			throw new IllegalArgumentException("Arguments must exist in the"
					+ " automaton, be different and not null.");
		}
		
		FairGameGraphChanges<LETTER, STATE> changes =
				new FairGameGraphChanges<LETTER, STATE>();
		boolean madeAChange = false;
		
		// Equalize states in both directions
		FairGameGraphChanges<LETTER, STATE> currentChange =
				equalizeBuechiStatesOneDir(secondState, firstState);
		if (currentChange != null) {
			changes.merge(currentChange, true);
			madeAChange = true;
		}
		currentChange = equalizeBuechiStatesOneDir(firstState, secondState);
		if (currentChange != null) {
			changes.merge(currentChange, true);
			madeAChange = true;
		}
		
		if (madeAChange) {
			return changes;
		} else {
			return null;
		}
	}
	
	@Override
	protected NestedWordAutomaton<LETTER, STATE> generateBuchiAutomatonFromGraph() {
		// TODO Currently returns a copy of the buechi automata.
		
		INestedWordAutomatonOldApi<LETTER, STATE> buechi = m_Buechi;
		@SuppressWarnings("unchecked")
		StateFactory<STATE> snf = (StateFactory<STATE>) new StringFactory();
		NestedWordAutomaton<LETTER, STATE> result = new NestedWordAutomaton<LETTER, STATE>(getServiceProvider(),
				buechi.getInternalAlphabet(), null, null, snf);

		// Add states
		for (STATE state : buechi.getStates()) {
			result.addState(buechi.isInitial(state), buechi.isFinal(state), state);
		}

		// Add edges
		for (STATE src : buechi.getStates()) {
			for (OutgoingInternalTransition<LETTER, STATE> trans : buechi.internalSuccessors(src)) {
				if (trans != null) {
					result.addInternalTransition(src, trans.getLetter(), trans.getSucc());
				}
			}
		}
		return result;
	}
	
	@Override
	protected void generateGameGraphFromBuechi() {
		INestedWordAutomatonOldApi<LETTER, STATE> buechi = m_Buechi;
		
		// Generate states
		for (STATE leftState : buechi.getStates()) {
			for (STATE rightState : buechi.getStates()) {
				// Generate Spoiler vertices (leftState, rightState)
				int priority = calculatePriority(leftState, rightState);
				if (priority == 1) {
					increaseGlobalInfinity();
				}
				SpoilerVertex<LETTER, STATE> spoilerVertex =
						new SpoilerVertex<LETTER, STATE>(priority, false, leftState, rightState);
				addSpoilerVertex(spoilerVertex);
				
				// Generate Duplicator vertices (leftState, rightState, letter)
				for (LETTER letter : buechi.lettersInternalIncoming(leftState)) {
					DuplicatorVertex<LETTER, STATE> duplicatorVertex =
							new DuplicatorVertex<LETTER, STATE>(2, false, leftState, rightState, letter);
					addDuplicatorVertex(duplicatorVertex);
				}
			}
		}

		increaseGlobalInfinity();

		// Generate edges
		for (STATE edgeDest : buechi.getStates()) {
			for (IncomingInternalTransition<LETTER, STATE> trans : buechi.internalPredecessors(edgeDest)) {
				for (STATE fixState : buechi.getStates()) {
					// Duplicator edges q1 -a-> q2 : (x, q1, a) -> (x, q2)
					Vertex<LETTER, STATE> src = getDuplicatorVertex(fixState, trans.getPred(), trans.getLetter(), false);
					Vertex<LETTER, STATE> dest = getSpoilerVertex(fixState, edgeDest, false);
					if (src != null && dest != null) {
						addEdge(src, dest);
					}

					// Spoiler edges q1 -a-> q2 : (q1, x) -> (q2, x, a)
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
	
	/**
	 * Assuming given transition does exist
	 * @param src
	 * @param a
	 * @param dest
	 * @return
	 */
	protected FairGameGraphChanges<LETTER, STATE> removeBuechiTransition(
			final STATE src, final LETTER a, final STATE dest) {
		Set<STATE> states = m_Buechi.getStates();
		if (src == null || dest == null
				|| !states.contains(src) || !states.contains(dest)) {
			throw new IllegalArgumentException("Arguments must exist in the"
					+ " automaton and not be null.");
		}
		GameGraphChangeType wasChangedBefore = m_ChangedBuechiTransitionsInverse.get(dest, a, src);
		if (wasChangedBefore != null && wasChangedBefore.equals(GameGraphChangeType.REMOVAL)) {
			// Transition was already removed previously
			return null;
		}
		
		FairGameGraphChanges<LETTER, STATE> changes =
				new FairGameGraphChanges<LETTER, STATE>();
		
		// Remove edges that were generated of this transition
		for (STATE fixState : states) {
			// Removal of edges must only be made to vertices of Duplicator
			// Duplicator edges q1 -a-> q2 : (x, q1, a) -> (x, q2, a)
			Vertex<LETTER, STATE> edgeSrc = getDuplicatorVertex(fixState, src, a, false);
			Vertex<LETTER, STATE> edgeDest = getSpoilerVertex(fixState, dest, false);
			if (src != null && dest != null) {
				removeEdge(edgeSrc, edgeDest);
				// Remember removal
				changes.removedEdge(edgeSrc, edgeDest);
			}
		}
		
		// Update set of changes
		m_ChangedBuechiTransitionsInverse.put(dest, a, src, GameGraphChangeType.REMOVAL);
		changes.removedBuechiTransition(src, a, dest);
		
		return changes;
	}
}
