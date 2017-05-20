/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.multipebble;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonForLetterBasedOnDemandConstruction;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.util.ISetOfPairs;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <STATE>
 *            state type
 */
public class FullMultipebbleGameAutomaton<LETTER, STATE, GS extends FullMultipebbleGameState<STATE>>
		extends NestedWordAutomatonForLetterBasedOnDemandConstruction<LETTER, GS> {

	private final AutomataLibraryServices mServices;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	private final FullMultipebbleStateFactory<STATE, GS> mStateFactory;
	private final GS mEmptyStackState;
	private final NestedMap2<STATE, STATE, GS> mGameStateMapping;
	private final Set<GS> mInitialStates;
	private final LETTER mInternalLetterForSpoilerWinningSink;
	private final LETTER mCallLetterForSpoilerWinningSink;

	public FullMultipebbleGameAutomaton(final AutomataLibraryServices services,
			final FullMultipebbleStateFactory<STATE, GS> gameFactory, final ISetOfPairs<STATE, ?> initialPairs,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand) {
		mServices = services;
		mOperand = operand;
		mStateFactory = gameFactory;
		mEmptyStackState = gameFactory.createEmptyStackState();
		mInitialStates = new HashSet<>();
		mGameStateMapping = new NestedMap2<>();
		if (mOperand.getVpAlphabet().getInternalAlphabet().isEmpty()) {
			mInternalLetterForSpoilerWinningSink = null;
			if (mOperand.getVpAlphabet().getCallAlphabet().isEmpty()) {
				throw new UnsupportedOperationException("Unsupported: automata where internal alphabet and call alphabet are empty.");
			}
			mCallLetterForSpoilerWinningSink = mOperand.getVpAlphabet().getCallAlphabet().iterator().next();
		} else {
			mInternalLetterForSpoilerWinningSink = mOperand.getVpAlphabet().getInternalAlphabet().iterator().next();
			mCallLetterForSpoilerWinningSink = null; 
		}
		constructInitialStates(initialPairs);
	}

	private void constructInitialStates(final ISetOfPairs<STATE, ?> initialPairs) {
		for (final Pair<STATE, STATE> pair : initialPairs) {
			final STATE q0 = pair.getFirst();
			final STATE q1 = pair.getSecond();
			if (!mStateFactory.isImmediatelyWinningForSpoiler(q0, q1, mOperand)) {
				final GS gs = mStateFactory.constructInitialState(q0, q1, mOperand);
				mGameStateMapping.put(q0, q1, gs);
				mInitialStates.add(gs);
			}
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new ToolchainCanceledException(this.getClass(),
						"constructing initial states of game automaton (already constructed: " + mInitialStates.size()
								+ " states");
			}
		}
	}

	public NestedMap2<STATE, STATE, GS> getGameStateMapping() {
		return mGameStateMapping;
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return mOperand.getVpAlphabet();
	}

	@Override
	public IStateFactory<GS> getStateFactory() {
		return mStateFactory;
	}

	@Override
	public int size() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public String sizeInformation() {
		return "has " + mInitialStates.size() + " initial states, number of all states yet unknown.";
	}

	@Override
	public GS getEmptyStackState() {
		return mEmptyStackState;
	}

	@Override
	public Iterable<GS> getInitialStates() {
		return mInitialStates;
	}

	@Override
	public boolean isInitial(final GS state) {
		return mInitialStates.contains(state);
	}

	@Override
	public boolean isFinal(final GS state) {
		return state.isAccepting();
	}

	@Override
	public Set<LETTER> lettersInternal(final GS state) {
		if (IFullMultipebbleAuxiliaryGameState.isSpoilerWinningSink(state)) {
			if (mInternalLetterForSpoilerWinningSink == null) {
				return Collections.emptySet();
			} else {
				return Collections.singleton(mInternalLetterForSpoilerWinningSink);
			}
		}
		return mOperand.lettersInternal(state.getSpoilerDoubleDecker().getUp());
	}

	@Override
	public Set<LETTER> lettersCall(final GS state) {
		if (IFullMultipebbleAuxiliaryGameState.isSpoilerWinningSink(state)) {
			if (mCallLetterForSpoilerWinningSink == null) {
				return Collections.emptySet();
			} else {
				return Collections.singleton(mCallLetterForSpoilerWinningSink);
			}
		}
		return mOperand.lettersCall(state.getSpoilerDoubleDecker().getUp());
	}
	
	@Override
	public Set<LETTER> lettersReturn(final GS state, final GS hier) {
		if (IFullMultipebbleAuxiliaryGameState.isSpoilerWinningSink(state)) {
			return Collections.emptySet();
		}
		return mOperand.lettersReturn(state.getSpoilerDoubleDecker().getUp(), hier.getSpoilerDoubleDecker().getUp());
	}


	@Override
	public Iterable<OutgoingInternalTransition<LETTER, GS>> internalSuccessors(final GS state, final LETTER letter) {
		final List<OutgoingInternalTransition<LETTER, GS>> result = new ArrayList<>();
		for (final GS succ : mStateFactory.computeSuccessorsInternal(state, letter, mOperand)) {
			result.add(new OutgoingInternalTransition<>(letter, succ));
		}
		return result;
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, GS>> callSuccessors(final GS state, final LETTER letter) {
		final List<OutgoingCallTransition<LETTER, GS>> result = new ArrayList<>();
		for (final GS succ : mStateFactory.computeSuccessorsCall(state, letter, mOperand)) {
			result.add(new OutgoingCallTransition<>(letter, succ));
		}
		return result;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, GS>> returnSuccessors(final GS state, final GS hier,
			final LETTER letter) {
		final List<OutgoingReturnTransition<LETTER, GS>> result = new ArrayList<>();
		for (final GS succ : mStateFactory.computeSuccessorsReturn(state, hier, letter, mOperand)) {
			result.add(new OutgoingReturnTransition<>(hier, letter, succ));
		}
		return result;
	}
}
