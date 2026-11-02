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

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

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

	Map<Pair<L, L>, IndependenceLetter<L>> mSpecialSymbols;
	private final Set<IndependenceLetter<L>> mAlphabet;
	private final VpAlphabet<IndependenceLetter<L>> mVpAlphabet;

	// TODO: do we need our own Implementation of IUnionStateFactory<S> or can we reuse an existing one?
	private final IUnionStateFactory<S> mFactory;
	private INwaOutgoingLetterAndTransitionProvider<IndependenceLetter<L>, S> mAutomaton;

	public IndependencyAutomaton(final Set<L> alphabet, final IUnionStateFactory<S> unionFactory) {
		mSpecialSymbols = new HashMap<>();
		mFactory = unionFactory;
		mAlphabet = new HashSet<>();

		for (final L letter : alphabet) {
			mAlphabet.add(IndependenceLetter.normal(letter));
		}

		for (final L letter1 : alphabet) {
			for (final L letter2 : alphabet) {

				final IndependenceLetter<L> specialSymbol = IndependenceLetter.special(letter1, letter2);
				if (!mAlphabet.add(specialSymbol)) {
					throw new IllegalArgumentException("Special symbol is not unique: " + specialSymbol);
				}
				mSpecialSymbols.put(new Pair<>(letter1, letter2), specialSymbol);
			}
		}
		mVpAlphabet = new VpAlphabet<>(mAlphabet, null, null);
	}

	@Override
	public Optional<IndependenceLetter<L>> getSpecialSymbol(final L letter1, final L letter2) {
		return Optional.ofNullable(mSpecialSymbols.get(new Pair<>(letter1, letter2)));
	}

	@Override
	public void addIndependence(final L letter1, final L letter2,
			final INwaOutgoingLetterAndTransitionProvider<IndependenceLetter<L>, S> automaton)
			throws AutomataLibraryException {

		// The given automaton needs to have letters of type IndependenceLetter<L>
		if (!mSpecialSymbols.containsKey(new Pair<>(letter1, letter2))) {
			throw new IllegalArgumentException("Unknown letter pair: " + letter1 + ", " + letter2);
		}

		if (!mVpAlphabet.equals(automaton.getVpAlphabet())) {
			throw new IllegalArgumentException("Automaton has a different alphabet.");
		}

		if (mAutomaton == null) {
			mAutomaton = automaton;
		} else {
			mAutomaton = new UnionNwa<>(mAutomaton, automaton, mFactory, false);
		}

	}

	@Override
	public VpAlphabet<IndependenceLetter<L>> getVpAlphabet() {
		return mVpAlphabet;
	}

	@Override
	public Set<IndependenceLetter<L>> getAlphabet() {
		return mAlphabet;
	}

	@Override
	public S getEmptyStackState() {
		if (mAutomaton == null) {
			return null;
		}
		return mAutomaton.getEmptyStackState();
	}

	@Override
	public Iterable<S> getInitialStates() {
		if (mAutomaton == null) {
			return Collections.emptySet();
		}
		return mAutomaton.getInitialStates();
	}

	@Override
	public boolean isInitial(final S state) {
		return mAutomaton != null && mAutomaton.isInitial(state);
	}

	@Override
	public boolean isFinal(final S state) {
		return mAutomaton != null && mAutomaton.isFinal(state);
	}

	@Override
	public int size() {
		return mAutomaton == null ? 0 : mAutomaton.size();
	}

	@Override
	public String sizeInformation() {
		return mAutomaton == null ? "Empty independency automaton" : mAutomaton.sizeInformation();
	}

	@Override
	public Iterable<OutgoingInternalTransition<IndependenceLetter<L>, S>> internalSuccessors(final S state,
			final IndependenceLetter<L> letter) {
		if (mAutomaton == null) {
			return Collections.emptySet();
		}
		return mAutomaton.internalSuccessors(state, letter);
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

	public static class IndependenceLetter<L1> {
		private final L1 mLetter1;
		private final L1 mLetter2;
		private final boolean mIsSpecial;

		private IndependenceLetter(final L1 letter1, final L1 letter2, final boolean isSpecial) {
			mLetter1 = letter1;
			mLetter2 = letter2;
			mIsSpecial = isSpecial;
		}

		public static <L> IndependenceLetter<L> normal(final L letter) {
			return new IndependenceLetter<>(letter, null, false);
		}

		public static <L> IndependenceLetter<L> special(final L letter1, final L letter2) {
			return new IndependenceLetter<>(letter1, letter2, true);
		}

		public boolean isSpecial() {
			return mIsSpecial;
		}

		public L1 getLetter1() {
			return mLetter1;
		}

		public L1 getLetter2() {
			return mLetter2;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (!(obj instanceof final IndependenceLetter<?> other)) {
				return false;
			}

			return mIsSpecial == other.mIsSpecial && Objects.equals(mLetter1, other.mLetter1)
					&& Objects.equals(mLetter2, other.mLetter2);
		}

		@Override
		public int hashCode() {
			return Objects.hash(mIsSpecial, mLetter1, mLetter2);
		}
	}

}
