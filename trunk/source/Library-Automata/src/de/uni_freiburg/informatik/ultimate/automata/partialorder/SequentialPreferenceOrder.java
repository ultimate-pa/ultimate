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
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SequentialPreferenceOrderAutomaton.ISequentialStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Either;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Order representing the sequentialization of two given orders mFirstOrder and mSecondOrder.
 *
 * @param <L>
 *            letter type
 * @param <S0>
 *            program state type
 * @param <S1>
 *            monitor state type of mFirstOrder
 * @param <S2>
 *            monitor state type of mSecondOrder
 * @param <S>
 *            monitor state type of the sequentialization
 */
public class SequentialPreferenceOrder<L, S0, S1, S2, S> implements IPreferenceOrder<L, S0, S> {
	private final IPreferenceOrder<L, S0, S1> mFirstOrder;
	private final IPreferenceOrder<L, S0, S2> mSecondOrder;
	private final ImmutableSet<L> mTransitionLetters;
	private final ISequentialStateFactory<S1, S2, S> mStateFactory;
	private final boolean mApplyFunctionAfterTransition;
	private SequentialPreferenceOrderAutomaton<L, S1, S2, S> mAutomaton;

	public SequentialPreferenceOrder(final IPreferenceOrder<L, S0, S1> fst, final IPreferenceOrder<L, S0, S2> snd,
			final ImmutableSet<L> transitionLetters, final ISequentialStateFactory<S1, S2, S> stateFactory,
			final boolean applyFunctionAfterTransition) {
		mFirstOrder = fst;
		mSecondOrder = snd;
		mTransitionLetters = transitionLetters;
		mStateFactory = stateFactory;
		mApplyFunctionAfterTransition = applyFunctionAfterTransition;
	}

	public static <L, S0, S1, S2> SequentialPreferenceOrder<L, S0, S1, S2, Either<S1, S2>> create(
			final IPreferenceOrder<L, S0, S1> fst, final IPreferenceOrder<L, S0, S2> snd,
			final ImmutableSet<L> transitionLetters) {
		return new SequentialPreferenceOrder<>(fst, snd, transitionLetters, new ISequentialStateFactory.Default<>(),
				true);
	}

	@Override
	public boolean isPositional() {
		return mFirstOrder.isPositional() || mSecondOrder.isPositional();
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<L, S> getMonitor() {
		if (mAutomaton == null) {
			mAutomaton = new SequentialPreferenceOrderAutomaton<>(mFirstOrder.getMonitor(), mSecondOrder.getMonitor(),
					mTransitionLetters, mStateFactory, mApplyFunctionAfterTransition);
		}
		return mAutomaton;
	}

	@Override
	public Comparator<L> getOrder(final S0 programState, final S monitorState) {
		switch (mStateFactory.getOriginalState(monitorState)) {
		case Either.Left(final S1 original):
			return mFirstOrder.getOrder(programState, original);
		case Either.Right(final S2 original):
			return mSecondOrder.getOrder(programState, original);
		}
	}
}
