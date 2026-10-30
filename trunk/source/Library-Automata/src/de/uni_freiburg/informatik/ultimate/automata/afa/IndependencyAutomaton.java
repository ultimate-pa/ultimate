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

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.UnionNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IUnionStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class IndependencyAutomaton<L, S> implements IIndependencyAutomaton<L, S> {

	Map<Pair<L, L>, L> mSpecialSymbols;
	// map from special symbols to their corresponding interpolant automaton (or union of automata)
	private final Map<L, INwaOutgoingLetterAndTransitionProvider<L, S>> mIndependenceAutomata;
	// TODO: we need a factory
	private IUnionStateFactory<S> mFactory;

	public IndependencyAutomaton() {
		mSpecialSymbols = new HashMap<>();
		mIndependenceAutomata = new HashMap<>();
	}

	@Override
	public Optional<L> getSpecialSymbol(final L letter1, final L letter2) {
		return Optional.ofNullable(mSpecialSymbols.get(new Pair<>(letter1, letter2)));
	}

	@Override
	public void addSpecialSymbol(final L letter1, final L letter2) {
		final Pair<L, L> pair = new Pair<>(letter1, letter2);

		mSpecialSymbols.computeIfAbsent(pair, p -> createSpecialSymbol(p));
	}

	private L createSpecialSymbol(final Pair<L, L> pair) {
		// TODO create a special symbol
		return null;
	}

	@Override
	public void addIndependence(final L specialSymbol, final INwaOutgoingLetterAndTransitionProvider<L, S> automaton)
			throws AutomataLibraryException {

		if (mIndependenceAutomata.containsKey(specialSymbol)) {
			mIndependenceAutomata.replace(specialSymbol,
					new UnionNwa<>(mIndependenceAutomata.get(specialSymbol), automaton, mFactory, false));

		} else {
			mIndependenceAutomata.put(specialSymbol, automaton);
		}
	}

	@Override
	public VpAlphabet<L> getVpAlphabet() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public S getEmptyStackState() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<S> getInitialStates() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isInitial(final S state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isFinal(final S state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public int size() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public String sizeInformation() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, S>> internalSuccessors(final S state, final L letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingCallTransition<L, S>> callSuccessors(final S state, final L letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, S>> returnSuccessors(final S state, final S hier, final L letter) {
		// TODO Auto-generated method stub
		return null;
	}

}
