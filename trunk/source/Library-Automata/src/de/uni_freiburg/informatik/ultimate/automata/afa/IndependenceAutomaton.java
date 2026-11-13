/*
 * Copyright (C) 2026 Marcel Ebbinghaus
 * Copyright (C) 2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.afa;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.afa.IndependenceLetter.IndependentPair;
import de.uni_freiburg.informatik.ultimate.automata.afa.IndependenceLetter.WrappedLetter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;

public class IndependenceAutomaton<L, S> implements INwaOutgoingLetterAndTransitionProvider<IndependenceLetter<L>, S> {

	private final IndependentPair<L> mIndependentPair;
	private final VpAlphabet<IndependenceLetter<L>> mAlphabet;
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mAutomaton;
	private final L mSpecialSymbol;

	public IndependenceAutomaton(final IndependentPair<L> pair, final L specialSymbol,
			final VpAlphabet<IndependenceLetter<L>> alphabet,
			final INwaOutgoingLetterAndTransitionProvider<L, S> automaton) {
		mIndependentPair = pair;
		mSpecialSymbol = specialSymbol;
		mAlphabet = alphabet;
		mAutomaton = automaton;
	}

	@Override
	public VpAlphabet<IndependenceLetter<L>> getVpAlphabet() {
		return mAlphabet;
	}

	@Override
	public S getEmptyStackState() {
		// no stack
		return null;
	}

	@Override
	public Iterable<S> getInitialStates() {
		return mAutomaton.getInitialStates();
	}

	@Override
	public boolean isInitial(final S state) {
		return mAutomaton.isInitial(state);
	}

	@Override
	public boolean isFinal(final S state) {
		return mAutomaton.isFinal(state);
	}

	@Override
	public int size() {
		return mAutomaton.size();
	}

	@Override
	public String sizeInformation() {
		return mAutomaton.sizeInformation();
	}

	@Override
	public Iterable<OutgoingInternalTransition<IndependenceLetter<L>, S>> internalSuccessors(final S state,
			final IndependenceLetter<L> letter) {
		return switch (letter) {
		case WrappedLetter<L>(final L wrappedLetter) ->
				wrapTransitions(mAutomaton.internalSuccessors(state, wrappedLetter), letter);

		case final IndependentPair<L> pair when pair.equals(mIndependentPair) ->
				wrapTransitions(mAutomaton.internalSuccessors(state, mSpecialSymbol), letter);

		default -> Collections.emptySet();
		};
	}

	private Iterable<OutgoingInternalTransition<IndependenceLetter<L>, S>> wrapTransitions(
			final Iterable<OutgoingInternalTransition<L, S>> transitions, final IndependenceLetter<L> letter) {

		final List<OutgoingInternalTransition<IndependenceLetter<L>, S>> result = new ArrayList<>();
		for (final var transition : transitions) {
			result.add(new OutgoingInternalTransition<>(letter, transition.getSucc()));
		}
		return result;
	}

	@Override
	public Iterable<OutgoingCallTransition<IndependenceLetter<L>, S>> callSuccessors(final S state,
			final IndependenceLetter<L> letter) {
		// not supported
		return null;
	}

	@Override
	public Iterable<OutgoingReturnTransition<IndependenceLetter<L>, S>> returnSuccessors(final S state, final S hier,
			final IndependenceLetter<L> letter) {
		// not supported
		return null;
	}

}
