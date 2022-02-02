/*
 * Copyright (C) 2022 Dennis Wölfing
 * Copyright (C) 2022 University of Freiburg
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

import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;

/**
 * A visitor that constructs an automaton containing all states and transitions visited by the underlying visitor.
 * Useful for debugging.
 *
 * @author Dennis Wölfing
 *
 * @param <L>
 *            The type of the letters of the automaton.
 * @param <S>
 *            The type of the states of the automaton.
 */
public class VisitedStateAutomatonConstructingVisitor<L, S> extends WrapperVisitor<L, S, IDfsVisitor<L, S>> {
	private final Predicate<S> mIsFinal;
	private final NestedWordAutomaton<L, S> mAutomaton;

	/**
	 * Constructor.
	 *
	 * @param underlying
	 *            The underlying visitor.
	 * @param isFinal
	 *            A predicate that determines whether a given state is final.
	 * @param alphabet
	 *            The alphabet of the automaton.
	 * @param services
	 *            An AutomataLibraryServices instance.
	 * @param stateFactory
	 *            An IEmptyStackStateFactory.
	 */
	public VisitedStateAutomatonConstructingVisitor(final IDfsVisitor<L, S> underlying, final Predicate<S> isFinal,
			final VpAlphabet<L> alphabet, final AutomataLibraryServices services,
			final IEmptyStackStateFactory<S> stateFactory) {
		super(underlying);
		mIsFinal = isFinal;
		mAutomaton = new NestedWordAutomaton<>(services, alphabet, stateFactory);
	}

	/**
	 * Constructor.
	 *
	 * @param underlying
	 *            The underlying visitor.
	 * @param operand
	 *            The operand that is being visited.
	 * @param services
	 *            An AutomataLibraryServices instance.
	 * @param stateFactory
	 *            An IEmptyStackStateFactory.
	 */
	public VisitedStateAutomatonConstructingVisitor(final IDfsVisitor<L, S> underlying,
			final INwaOutgoingLetterAndTransitionProvider<L, S> operand, final AutomataLibraryServices services,
			final IEmptyStackStateFactory<S> stateFactory) {
		this(underlying, operand::isFinal, operand.getVpAlphabet(), services, stateFactory);
	}

	@Override
	public boolean discoverTransition(final S source, final L letter, final S target) {
		if (!mAutomaton.contains(target)) {
			mAutomaton.addState(false, mIsFinal.test(target), target);
		}
		mAutomaton.addInternalTransition(source, letter, target);

		return super.discoverTransition(source, letter, target);
	}

	@Override
	public boolean addStartState(final S state) {
		mAutomaton.addState(true, mIsFinal.test(state), state);
		return super.addStartState(state);
	}

	public NestedWordAutomaton<L, S> getAutomaton() {
		return mAutomaton;
	}
}
