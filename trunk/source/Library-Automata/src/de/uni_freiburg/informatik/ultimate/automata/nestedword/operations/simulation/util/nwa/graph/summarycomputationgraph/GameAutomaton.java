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
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonOnDemandStateAndLetter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.SpoilerNwaVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.GameLetter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.GameSpoilerNwaVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.IGameState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Construct game automaton given the input automaton (not a game graph) and
 * the initial partition.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <STATE>
 */
public abstract class GameAutomaton<LETTER, STATE> extends NestedWordAutomatonOnDemandStateAndLetter<GameLetter<LETTER, STATE>, IGameState> {
	
	private final boolean mOmitSymmetricPairs = true;
	
	private final Collection<Set<STATE>> mPossibleEquivalentClasses;
	private final IDoubleDeckerAutomaton<LETTER, STATE> mOperand;
	
	
	public GameAutomaton(final AutomataLibraryServices services, final IStateFactory<IGameState> stateFactory,
			final Collection<Set<STATE>> possibleEquivalentClasses, final IDoubleDeckerAutomaton<LETTER, STATE> operand) {
		super(services, stateFactory);
		mPossibleEquivalentClasses = possibleEquivalentClasses;
		mOperand = operand;
	}
	@Override
	protected void constructInitialStates() {
		for (final Set<STATE> eqClass : mPossibleEquivalentClasses) {
			for (final STATE q0 : eqClass) {
				for (final STATE q1 : eqClass) {
					if (mOmitSymmetricPairs && q0.equals(q1)) {
						// omit pair
					} else {
						addInitialVertex(q0, q1);
					}
				}
			}
		}
	}

	private void addInitialVertex(final STATE q0, final STATE q1) {
		final GameSpoilerNwaVertex<LETTER, STATE> wrapper = constuctInitialWrappedVertex(q0, q1);
		super.mCache.addState(true, true, wrapper);
	}
	private GameSpoilerNwaVertex<LETTER, STATE> constuctInitialWrappedVertex(final STATE q0, final STATE q1) {
		final SpoilerNwaVertex<LETTER, STATE> vertex = constructInitialVertex(q0, q1);
		return new GameSpoilerNwaVertex<>(vertex);
	}
	protected abstract SpoilerNwaVertex<LETTER, STATE> constructInitialVertex(STATE q0, STATE q1);
	
	
	@Override
	protected void constructInternalSuccessors(final IGameState state) {
		if (isSpoilerSink(state) || isDuplicatorSink(state)) {
			// do nothing
		} else {
			final GameSpoilerNwaVertex<LETTER, STATE> wrapper = (GameSpoilerNwaVertex<LETTER, STATE>) state;
			final SpoilerNwaVertex<LETTER, STATE> vertex = wrapper.getSpoilerNwaVertex();
			final STATE spoilerState = vertex.getQ0();
			final STATE duplicatorState = vertex.getQ1();
			for (final LETTER letter : mOperand.lettersInternal(spoilerState)) {
				final Iterable<OutgoingInternalTransition<LETTER, STATE>> spoilerSuccIt = mOperand.internalSuccessors(spoilerState, letter);
				final Set<STATE> spoilerSuccs = NestedWordAutomataUtils.constructSuccessorSet(spoilerSuccIt);
				final Iterable<OutgoingInternalTransition<LETTER, STATE>> duplicatorSuccIt = mOperand.internalSuccessors(duplicatorState, letter);
				final Set<STATE> duplicatorSuccs = NestedWordAutomataUtils.constructSuccessorSet(duplicatorSuccIt);
				final HashRelation<GameLetter<LETTER, STATE>, IGameState> succTrans = computerSuccessorTransitions(vertex, letter, spoilerSuccs, duplicatorSuccs);

				
				
			}

		}
		// TODO Auto-generated method stub
		
	}
	
	private HashRelation<GameLetter<LETTER, STATE>, IGameState> computerSuccessorTransitions(
			final SpoilerNwaVertex<LETTER, STATE> vertex, final LETTER letter, final Set<STATE> spoilerSuccs,
			final Set<STATE> duplicatorSuccs) {
		final HashRelation<GameLetter<LETTER, STATE>, IGameState> result = new HashRelation<>();
		for (final STATE spoilerSucc : spoilerSuccs) {
			final GameLetter<LETTER, STATE> gameLetter = getOrConstuctGameLetter(vertex, letter, spoilerSucc);
			for (final STATE duplicatorSucc : duplicatorSuccs) {
				final IGameState wrapper = getOrConstructVertex(vertex, letter, spoilerSucc, duplicatorSucc);
				result.addPair(gameLetter, wrapper);
			}
		}
		return result;
	}
	private IGameState getOrConstructVertex(final SpoilerNwaVertex<LETTER, STATE> vertex, final LETTER letter, final STATE spoilerSucc,
			final STATE duplicatorSucc) {
		// TODO Auto-generated method stub
		return null;
	}
	private GameLetter<LETTER, STATE> getOrConstuctGameLetter(final SpoilerNwaVertex<LETTER, STATE> vertex, final LETTER letter,
			final STATE spoilerSucc) {
		// TODO Auto-generated method stub
		return null;
	}
	private boolean isDuplicatorSink(final IGameState state) {
		// TODO Auto-generated method stub
		return false;
	}
	private boolean isSpoilerSink(final IGameState state) {
		// TODO Auto-generated method stub
		return false;
	}
	@Override
	protected void constructCallSuccessors(final IGameState state) {
		// TODO Auto-generated method stub
		
	}
	@Override
	protected void constructReturnSuccessors(final IGameState lin, final IGameState hier) {
		// TODO Auto-generated method stub
		
	}

}
