/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.TransitionType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.DuplicatorNwaVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.DuplicatorSubSummaryChoiceVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.DuplicatorWinningSink;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.SpoilerNwaVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.SpoilerSubSummaryPriorityVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.IGameLetter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.IGameState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;

/**
 * Construct game graph from given game automaton.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class GameAutomatonToGameGraphTransformer<LETTER, STATE> {

	private final INestedWordAutomaton<IGameLetter<LETTER, STATE>, IGameState> mGameAutomaton;
	private final AGameGraph<LETTER, STATE> mGameGraph;
	private final SpoilerNwaVertex<LETTER, STATE> mSpoilerWinningSink;
	private final DuplicatorNwaVertex<LETTER, STATE> mDuplicatorWinningSink;
	private AutomataLibraryServices mServices;

	public GameAutomatonToGameGraphTransformer(final AutomataLibraryServices services,
			final INestedWordAutomaton<IGameLetter<LETTER, STATE>, IGameState> gameAutomaton,
			final SpoilerNwaVertex<LETTER, STATE> spoilerWinningSink, final INestedWordAutomaton<LETTER, STATE> operand,
			final Collection<GameCallReturnSummary<STATE>> gameSummaries) throws AutomataOperationCanceledException {
		super();
		mServices = services;
		mGameAutomaton = gameAutomaton;
		mSpoilerWinningSink = spoilerWinningSink;
		mDuplicatorWinningSink = new DuplicatorNwaVertex<>(0, false, null, null, null, TransitionType.SINK,
				new DuplicatorWinningSink<>(null));
		mGameGraph = new AGameGraph<LETTER, STATE>(mServices, null, null, null, operand) {

			@Override
			public INestedWordAutomaton<LETTER, STATE> generateAutomatonFromGraph()
					throws AutomataOperationCanceledException {
				// TODO Auto-generated method stub
				return null;
			}

			@Override
			public void generateGameGraphFromAutomaton() throws AutomataOperationCanceledException {
				// TODO Auto-generated method stub

			}
		};

		for (final IGameState gameState : mGameAutomaton.getStates()) {
			addSpoilerVertex(gameState);
			boolean hasOutgoingInternalTransitions = false;
			for (final OutgoingInternalTransition<IGameLetter<LETTER, STATE>, IGameState> trans : mGameAutomaton
					.internalSuccessors(gameState)) {
				hasOutgoingInternalTransitions = true;
				addDuplicatorVertex(trans.getLetter());
				addSpoilerVertex(trans.getSucc());
				addEdges(gameState, trans.getLetter(), trans.getSucc());
			}
			boolean hasOutgoingCallTransitions = false;
			for (final OutgoingCallTransition<IGameLetter<LETTER, STATE>, IGameState> trans : mGameAutomaton
					.callSuccessors(gameState)) {
				hasOutgoingCallTransitions = true;
				addDuplicatorVertex(trans.getLetter());
				addSpoilerVertex(trans.getSucc());
				addEdges(gameState, trans.getLetter(), trans.getSucc());
			}
			if (!hasOutgoingInternalTransitions && !hasOutgoingCallTransitions) {
				addEdgeToDuplicatorSink(gameState);
			}
		}

		for (final GameCallReturnSummary<STATE> gameSummary : gameSummaries) {
			addGameSummary(gameSummary);
		}
		// global infinity has to be one plus the number of prio 1 nodes
		mGameGraph.increaseGlobalInfinity();
	}

	private SpoilerNwaVertex<LETTER, STATE> getSpoilerVertex(final IGameState gameState) {
		if (GameAutomaton.isSpoilerSink(gameState)) {
			return mSpoilerWinningSink;
		}
		return GameAutomaton.unwrapSpoilerNwaVertex(gameState);
	}

	private void addEdgeToDuplicatorSink(final IGameState gameState) {
		mGameGraph.addEdge(getSpoilerVertex(gameState), mDuplicatorWinningSink);
	}

	private void addEdges(final IGameState gameState, final IGameLetter<LETTER, STATE> letter, final IGameState succ) {
		mGameGraph.addEdge(getSpoilerVertex(gameState), (Vertex<LETTER, STATE>) letter);
		mGameGraph.addEdge((Vertex<LETTER, STATE>) letter, getSpoilerVertex(succ));
	}

	private void addDuplicatorVertex(final IGameLetter<LETTER, STATE> letter) {
		if (!mGameGraph.getDuplicatorVertices().contains(letter)) {
			mGameGraph.addDuplicatorVertex((DuplicatorVertex<LETTER, STATE>) letter);
		}
	}

	private void addSpoilerVertex(final IGameState gameState) {
		final SpoilerNwaVertex<LETTER, STATE> spoilerVertex = getSpoilerVertex(gameState);
		if (!mGameGraph.getSpoilerVertices().contains(spoilerVertex)) {
			mGameGraph.addSpoilerVertex(spoilerVertex);
			if (spoilerVertex.getPriority() == 1) {
				mGameGraph.increaseGlobalInfinity();
			}
			if (spoilerVertex == mSpoilerWinningSink) {
				mGameGraph.addEdge(mSpoilerWinningSink, mSpoilerWinningSink);
			}
		}
	}

	private void addGameSummary(final GameCallReturnSummary<STATE> gameSummary) {
		final SpoilerNwaVertex<LETTER, STATE> sourceVertex = getSpoilerVertex(gameSummary.getSummarySource());
		assert mGameGraph.getSpoilerVertices().contains(sourceVertex) : "source missing";
		final DuplicatorSubSummaryChoiceVertex<LETTER, STATE> duplicatorChoice =
				new DuplicatorSubSummaryChoiceVertex<>(gameSummary);
		assert !mGameGraph.getDuplicatorVertices().contains(duplicatorChoice) : "duplicator choice already there";
		mGameGraph.addDuplicatorVertex(duplicatorChoice);
		mGameGraph.addEdge(sourceVertex, duplicatorChoice);
		for (final IGameState duplicatorResponse : gameSummary.getDuplicatorResponses().keySet()) {
			final SpoilerSubSummaryPriorityVertex<LETTER, STATE> spoilerPrioVertex =
					new SpoilerSubSummaryPriorityVertex<>(gameSummary, duplicatorResponse);
			assert !mGameGraph.getSpoilerVertices()
					.contains(spoilerPrioVertex) : "spoiler priority vertex already there";
			mGameGraph.addSpoilerVertex(spoilerPrioVertex);
			final SpoilerNwaVertex<LETTER, STATE> targetVertex = getSpoilerVertex(duplicatorResponse);
			assert mGameGraph.getSpoilerVertices().contains(targetVertex) : "target missing";
			mGameGraph.addEdge(duplicatorChoice, spoilerPrioVertex);
			mGameGraph.addEdge(spoilerPrioVertex, targetVertex);
		}
	}

	public AGameGraph<LETTER, STATE> getResult() {
		return mGameGraph;
	}

}
