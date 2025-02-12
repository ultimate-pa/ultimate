/*
 * Copyright (C) 2024 Emma Bach
 * Copyright (C) 2024 Marcel Ebbinghaus
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.Comparator;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IfElsePreferenceOrderAutomaton.IIfElseStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Order representing a combination of two given orders mFirstOrder and mSecondOrder that chooses which of the two
 * monitors to use based on which branch of an if-statement the program enters.
 *
 * @param <L>
 *            The type of the transition letters.
 * @param <S0>
 *            The state type of the program.
 * @param <S1>
 *            The state type of mLeftAutomaton.
 * @param <S2>
 *            The state type of mRightAutomaton.
 * @param <S>
 *            The state type of the combination. If mAutomaton is using the default state factory, this will be
 *            {@code OptionalEither<S1,S2>}.
 */
public class IfElsePreferenceOrder<L, S0, S1, S2, S> implements IPreferenceOrder<L, S0, S> {

	private final IPreferenceOrder<L, S0, S1> mFirstOrder;
	private final IPreferenceOrder<L, S0, S2> mSecondOrder;
	private final IIfElseStateFactory<S1, S2, S> mStateFactory;
	private final IfElsePreferenceOrderAutomaton<L, S1, S2, S> mAutomaton;

	public IfElsePreferenceOrder(final IPreferenceOrder<L, S0, S1> fst, final IPreferenceOrder<L, S0, S2> snd,
			final ImmutableSet<L> ifBranchLetters, final IIfElseStateFactory<S1, S2, S> stateFactory) {
		mFirstOrder = fst;
		mSecondOrder = snd;
		mStateFactory = stateFactory;
		mAutomaton =
				new IfElsePreferenceOrderAutomaton<>(fst.getMonitor(), snd.getMonitor(), ifBranchLetters, stateFactory);
	}

	public static <L, S0, S1, S2> IfElsePreferenceOrder<L, S0, S1, S2, ?> create(final IPreferenceOrder<L, S0, S1> fst,
			final IPreferenceOrder<L, S0, S2> snd, final ImmutableSet<L> ifBranchLetters) {
		return new IfElsePreferenceOrder<>(fst, snd, ifBranchLetters, new IIfElseStateFactory.Default<>());
	}

	@Override
	public boolean isPositional() {
		return mFirstOrder.isPositional() || mSecondOrder.isPositional();
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<L, S> getMonitor() {
		return mAutomaton;
	}

	@Override
	public Comparator<L> getOrder(final S0 programState, final S monitorState) {
		switch (mStateFactory.getOriginalState(monitorState)) {
		case IfThenElseState.Initial():
			// Lambda Expression representing the empty order
			return (a, b) -> 0;
		case IfThenElseState.Then(final S1 original):
			return mFirstOrder.getOrder(programState, original);
		case IfThenElseState.Else(final S2 original):
			return mSecondOrder.getOrder(programState, original);
		}
	}
}
