/*
 * Copyright (C) 2020 Marcel Ebbinghaus
 * Copyright (C) 2020 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors;

import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;

/**
 * A visitor that explicitly constructs the traversed automaton.
 *
 * @author Marcel Ebbinghaus
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters in the automaton
 * @param <S>
 *            The type of automaton states
 */
public class AutomatonConstructingVisitor<L, S> implements IDfsVisitor<L, S> {
	private final Predicate<S> mIsInitial;
	private final Predicate<S> mIsFinal;
	private final NestedWordAutomaton<L, S> mReductionAutomaton;

	/**
	 * Create a new visitor instance that constructs a sub-automaton of a given automaton. This can e.g. be used for
	 * sleep set reductions with delay sets.
	 *
	 * @param operand
	 *            The unreduced automaton, used to identify the alphabet, initial and final states
	 * @param services
	 *            Services used in the constructed automaton
	 * @param stateFactory
	 *            State factory used by the constructed automaton
	 */
	public AutomatonConstructingVisitor(final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final AutomataLibraryServices services, final IEmptyStackStateFactory<S> stateFactory) {
		this(operand::isInitial, operand::isFinal, operand.getVpAlphabet(), services, stateFactory);
	}

	/**
	 * Create a new visitor instance.
	 *
	 * @param isInitial
	 *            Used to identify initial states in the constructed automaton
	 * @param isFinal
	 *            Used to identify final states in the constructed automaton
	 * @param alphabet
	 *            The alphabet of the constructed automaton
	 * @param services
	 *            Services used in the constructed automaton
	 * @param stateFactory
	 *            State factory used by the constructed automaton
	 */
	public AutomatonConstructingVisitor(final Predicate<S> isInitial, final Predicate<S> isFinal,
			final VpAlphabet<L> alphabet, final AutomataLibraryServices services,
			final IEmptyStackStateFactory<S> stateFactory) {
		mIsInitial = isInitial;
		mIsFinal = isFinal;
		mReductionAutomaton = new NestedWordAutomaton<>(services, alphabet, stateFactory);
	}

	@Override
	public boolean discoverTransition(final S source, final L letter, final S target) {
		// add succState to the automaton
		if (!mReductionAutomaton.contains(target)) {
			mReductionAutomaton.addState(mIsInitial.test(target), mIsFinal.test(target), target);
		}
		// add transition from currentState to succState to the automaton
		mReductionAutomaton.addInternalTransition(source, letter, target);
		return false;
	}

	@Override
	public boolean addStartState(final S state) {
		mReductionAutomaton.addState(true, mIsFinal.test(state), state);
		return false;
	}

	public NestedWordAutomaton<L, S> getReductionAutomaton() {
		return mReductionAutomaton;
	}
}
