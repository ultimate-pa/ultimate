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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.afa.NaiveUnionNwa.UnionState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;

// TODO: I've implemented this class in the afa package for now, but we should move it later
public class NaiveUnionNwa<L, S> implements INwaOutgoingLetterAndTransitionProvider<L, UnionState<S>> {

	private final List<INwaOutgoingLetterAndTransitionProvider<L, S>> mAutomata;
	private final VpAlphabet<L> mVpAlphabet;
	private final List<UnionState<S>> mInitialStates;

	public NaiveUnionNwa(final List<INwaOutgoingLetterAndTransitionProvider<L, S>> automata) {

		if (automata.isEmpty()) {
			throw new IllegalArgumentException("At least one automaton is required.");
		}

		// automata has to be a list of total INwaOutgoingLetterAndTransitionProvider
		mAutomata = List.copyOf(automata);
		mVpAlphabet = mAutomata.getFirst().getVpAlphabet();

		final List<UnionState<S>> initialStates = new ArrayList<>();

		for (int i = 0; i < mAutomata.size(); i++) {
			final var automaton = mAutomata.get(i);

			if (!mVpAlphabet.equals(automaton.getVpAlphabet())) {
				throw new IllegalArgumentException("All automata must have the same VpAlphabet.");
			}

			for (final S initialState : automaton.getInitialStates()) {
				initialStates.add(new UnionState<>(i, initialState));
			}
		}
		mInitialStates = List.copyOf(initialStates);
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, UnionState<S>>> internalSuccessors(final UnionState<S> state,
			final L letter) {

		final var automaton = getAutomaton(state);
		final List<OutgoingInternalTransition<L, UnionState<S>>> result = new ArrayList<>();

		for (final var transition : automaton.internalSuccessors(state.state(), letter)) {
			result.add(new OutgoingInternalTransition<>(letter,
					new UnionState<>(state.automatonId(), transition.getSucc())));
		}
		return result;
	}

	private INwaOutgoingLetterAndTransitionProvider<L, S> getAutomaton(final UnionState<S> state) {

		final int id = state.automatonId();

		if (id < 0 || id >= mAutomata.size()) {
			throw new IllegalArgumentException("Invalid automaton ID: " + id);
		}
		return mAutomata.get(id);
	}

	@Override
	public Iterable<OutgoingCallTransition<L, UnionState<S>>> callSuccessors(final UnionState<S> state,
			final L letter) {
		// not supported
		return null;
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, UnionState<S>>> returnSuccessors(final UnionState<S> state,
			final UnionState<S> hier, final L letter) {
		// not supported
		return null;
	}

	@Override
	public VpAlphabet<L> getVpAlphabet() {
		return mVpAlphabet;
	}

	@Override
	public UnionState<S> getEmptyStackState() {
		// no stack
		return null;
	}

	@Override
	public Iterable<UnionState<S>> getInitialStates() {
		return mInitialStates;
	}

	@Override
	public boolean isInitial(final UnionState<S> state) {
		return getAutomaton(state).isInitial(state.state());
	}

	@Override
	public boolean isFinal(final UnionState<S> state) {
		return getAutomaton(state).isFinal(state.state());
	}

	@Override
	public int size() {
		int result = 0;
		for (final var automaton : mAutomata) {
			if (automaton.size() < 0) {
				return -1;
			}
			result += automaton.size();
		}
		return result;
	}

	@Override
	public String sizeInformation() {
		return "currently " + size() + " states, but on-demand construction may add more states";
	}

	public record UnionState<S>(int automatonId, S state) {
	}

}