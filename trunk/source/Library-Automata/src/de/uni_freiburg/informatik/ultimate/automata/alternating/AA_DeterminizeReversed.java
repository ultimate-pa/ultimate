/*
 * Copyright (C) 2015 Carl Kuesters
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.alternating;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class AA_DeterminizeReversed<LETTER> extends GeneralOperation<LETTER, BitSet, IStateFactory<BitSet>> {
	private final NestedWordAutomaton<LETTER, BitSet> mResultAutomaton;

	public AA_DeterminizeReversed(final AutomataLibraryServices services,
			final AlternatingAutomaton<LETTER, BitSet> alternatingAutomaton,
			final IEmptyStackStateFactory<BitSet> emtpyStackStateFactory) {
		super(services);
		final VpAlphabet<LETTER> vpAlphabet = new VpAlphabet<LETTER>(alternatingAutomaton.getAlphabet(),
				Collections.emptySet(), Collections.emptySet());
		mResultAutomaton = new NestedWordAutomaton<>(services, vpAlphabet, emtpyStackStateFactory);
		final LinkedList<BitSet> newStates = new LinkedList<>();
		newStates.add(alternatingAutomaton.getFinalStatesBitVector());
		final List<Pair<BitSet, Pair<LETTER, BitSet>>> transitionsToAdd = new ArrayList<>();
		while (!newStates.isEmpty()) {
			final BitSet state = newStates.getFirst();
			final boolean isInitial = state == alternatingAutomaton.getFinalStatesBitVector();
			final boolean isFinal = alternatingAutomaton.getAcceptingFunction().getResult(state);
			mResultAutomaton.addState(isInitial, isFinal, state);
			for (final LETTER letter : alternatingAutomaton.getAlphabet()) {
				final BitSet nextState = (BitSet) state.clone();
				alternatingAutomaton.resolveLetter(letter, nextState);
				final boolean addTransitionDirectly;
				if (!mResultAutomaton.getStates().contains(nextState)) {
					if (!newStates.contains(nextState)) {
						addTransitionDirectly = false;
						newStates.add(nextState);
					} else {
						addTransitionDirectly = true;
					}
				} else {
					addTransitionDirectly = true;
				}
				/*
				 * Christian 2016-08-19: fixed a bug: If the state is not in the automaton, adding transitions will
				 *     fail. That is why I added this list of transitions to add later in the hope that this should fix
				 *     the problem.
				 */
				if (addTransitionDirectly) {
					mResultAutomaton.addInternalTransition(state, letter, nextState);
				} else {
					final Pair<LETTER, BitSet> innerPair = new Pair<>(letter, nextState);
					transitionsToAdd.add(new Pair<>(state, innerPair));
				}
			}
			newStates.removeFirst();
		}
		for (final Pair<BitSet, Pair<LETTER, BitSet>> transition : transitionsToAdd) {
			final Pair<LETTER, BitSet> innerPair = transition.getSecond();
			mResultAutomaton.addInternalTransition(transition.getFirst(), innerPair.getFirst(), innerPair.getSecond());
		}
	}

	@Override
	public INestedWordAutomaton<LETTER, BitSet> getResult() {
		return mResultAutomaton;
	}
}
