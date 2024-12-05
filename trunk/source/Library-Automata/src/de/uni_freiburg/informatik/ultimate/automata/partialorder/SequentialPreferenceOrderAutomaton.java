/*
 * Copyright (C) 2024 Marcel Ebbinghaus
 * Copyright (C) 2024 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Automaton representing the monitor of the sequentialization of two given orders fst and snd.
 *
 * @param <L>
 *            letter type
 * @param <S>
 *            state type
 */
public class SequentialPreferenceOrderAutomaton<L extends IAction, S>
		implements INwaOutgoingLetterAndTransitionProvider<L, S> {

	private final INwaOutgoingLetterAndTransitionProvider<L, S> mLeftAutomaton;
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mRightAutomaton;
	private final ImmutableSet<L> mTransitionLetters;

	public SequentialPreferenceOrderAutomaton(final INwaOutgoingLetterAndTransitionProvider<L, S> leftAutomaton,
			final INwaOutgoingLetterAndTransitionProvider<L, S> rightAutomaton,
			final ImmutableSet<L> transitionLetters) {
		mLeftAutomaton = leftAutomaton;
		mRightAutomaton = rightAutomaton;
		mTransitionLetters = transitionLetters;
	}

	@Override
	public IStateFactory<S> getStateFactory() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VpAlphabet<L> getVpAlphabet() {
		// Currently we assume both automata have the same alphabet,
		// so it doesn't matter which one gets returned
		// TODO Maybe return the union instead just to make sure?
		return mLeftAutomaton.getVpAlphabet();
	}

	@Override
	public S getEmptyStackState() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<S> getInitialStates() {
		return mLeftAutomaton.getInitialStates();
	}

	@Override
	public boolean isInitial(final S state) {
		// TODO Maybe this could lead to problems if S is not a state of mLeftAutomaton?
		return mLeftAutomaton.isInitial(state);
	}

	@Override
	public boolean isFinal(final S state) {
		return mRightAutomaton.isFinal(state);
	}

	@Override
	public int size() {
		return mLeftAutomaton.size() + mRightAutomaton.size();
	}

	@Override
	public String sizeInformation() {
		return "The first automaton has " + mLeftAutomaton.size() + " states, while the second one has "
				+ mRightAutomaton.size() + ".";
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, S>> internalSuccessors(final S state, final L letter) {
		if (mLeftAutomaton.isFinal(state) && mTransitionLetters.contains(letter)) {
			// Transition from the final states of mLeftAutomaton to the initial state of mRightAutomaton
			return Set
					.of(new OutgoingInternalTransition<>(letter, mRightAutomaton.getInitialStates().iterator().next()));
		}
		return null;
	}

	@Override
	public Iterable<OutgoingCallTransition<L, S>> callSuccessors(final S state, final L letter) {
		// Not needed because recursion is not supported
		return null;
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, S>> returnSuccessors(final S state, final S hier, final L letter) {
		// Not needed because recursion is not supported
		return null;
	}

}
