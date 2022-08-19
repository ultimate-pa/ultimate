/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.IteratorConcatenation;

/**
 * This {@link INwaOutgoingLetterAndTransitionProvider} represents the
 * modification of another {@link INwaOutgoingLetterAndTransitionProvider}. The
 * input {@link INwaOutgoingLetterAndTransitionProvider} is however not modified
 * at all. An {@link AutomatonWithImplicitSelfloops} is just a layer that acts
 * as a modification and uses the input automaton as back-end. For all STATE-LETTER
 * pairs that in the set product of mLooperStates and mLooperLetters the
 * {@link AutomatonWithImplicitSelfloops} has a self-loop (and no other outgoing
 * transitions), for other LETTERs the {@link AutomatonWithImplicitSelfloops}
 * has the transitions of the input
 * {@link INwaOutgoingLetterAndTransitionProvider}.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class AutomatonWithImplicitSelfloops<LETTER, STATE>
		implements INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> {
	protected final AutomataLibraryServices mServices;
	protected final ILogger mLogger;
	protected final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mInputAutomaton;
	protected final Set<LETTER> mLooperLetters;
	protected final Predicate<STATE> mLooperStates;

	public AutomatonWithImplicitSelfloops(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> inputAutomaton,
			final Set<LETTER> loopersLetters, final Predicate<STATE> looperStates) {
		super();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		if (!NestedWordAutomataUtils.isFiniteAutomaton(inputAutomaton)) {
			throw new UnsupportedOperationException("Calls and returns are not yet supported.");
		}
		mInputAutomaton = inputAutomaton;
		mLooperLetters = loopersLetters;
		mLooperStates = looperStates;
	}

	public AutomatonWithImplicitSelfloops(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> inputAutomaton,
			final Set<LETTER> loopersLetters) {
		this(services, inputAutomaton, loopersLetters, x -> true);
	}

	@Override
	public int size() {
		return mInputAutomaton.size();
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mInputAutomaton.getAlphabet();
	}

	@Override
	public String sizeInformation() {
		return mInputAutomaton.size() + " states.";
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return mInputAutomaton.getVpAlphabet();
	}

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mInputAutomaton.getStateFactory();
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		return mInputAutomaton.getInitialStates();
	}

	@Override
	public boolean isInitial(final STATE state) {
		return mInputAutomaton.isInitial(state);
	}

	@Override
	public boolean isFinal(final STATE state) {
		return mInputAutomaton.isFinal(state);
	}

	@Override
	public STATE getEmptyStackState() {
		return mInputAutomaton.getEmptyStackState();
	}

	@Override
	public Set<LETTER> lettersInternal(final STATE state) {
		if (mLooperStates.test(state)) {
			final Set<LETTER> letters = new HashSet<>();
			for (final OutgoingInternalTransition<LETTER, STATE> outTrans : internalSuccessors(state)) {
				letters.add(outTrans.getLetter());
			}
			return letters;
		} else {
			return mInputAutomaton.lettersInternal(state);
		}
	}

	@Override
	public Set<LETTER> lettersCall(final STATE state) {
		return Collections.emptySet();
	}

	@Override
	public Set<LETTER> lettersReturn(final STATE state, final STATE hier) {
		return Collections.emptySet();
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state,
			final LETTER letter) {
		if (mLooperStates.test(state)) {
			if (mLooperLetters.contains(letter)) {
				return Collections.singleton(new OutgoingInternalTransition(letter, state));
			} else {
				return mInputAutomaton.internalSuccessors(state, letter);
			}
		} else {
			return mInputAutomaton.internalSuccessors(state, letter);
		}
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state) {
		if (mLooperStates.test(state)) {
			// TODO 2019-10-15 Matthias: Make this method efficient if required.
			final List<Iterator<OutgoingInternalTransition<LETTER, STATE>>> iterators = new ArrayList<>();
			for (final LETTER letter : mInputAutomaton.getAlphabet()) {
				iterators.add(internalSuccessors(state, letter).iterator());
			}
			return new Iterable<OutgoingInternalTransition<LETTER, STATE>>() {

				@Override
				public Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator() {
					return new IteratorConcatenation<OutgoingInternalTransition<LETTER, STATE>>(iterators);
				}

			};
		} else {
			return mInputAutomaton.internalSuccessors(state);
		}
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter) {
		throw new UnsupportedOperationException("does not support call and return");
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state) {
		return Collections.emptyList();
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier,
			final LETTER letter) {
		return Collections.emptyList();
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(final STATE state,
			final STATE hier) {
		return Collections.emptyList();
	}

	@Override
	public String toString() {
		return (AutomatonDefinitionPrinter.toString(mServices, "nwa", this));
	}


	private static class ContainsAny<E> implements Set<E> {

		@Override
		public boolean add(final E arg0) {
			throw new UnsupportedOperationException("ContainsAny supports only contains");
		}

		@Override
		public boolean addAll(final Collection<? extends E> arg0) {
			throw new UnsupportedOperationException("ContainsAny supports only contains");
		}

		@Override
		public void clear() {
			throw new UnsupportedOperationException("ContainsAny supports only contains");
		}

		@Override
		public boolean contains(final Object arg0) {
			return true;
		}

		@Override
		public boolean containsAll(final Collection<?> arg0) {
			return true;
		}

		@Override
		public boolean isEmpty() {
			throw new UnsupportedOperationException("ContainsAny supports only contains");
		}

		@Override
		public Iterator<E> iterator() {
			throw new UnsupportedOperationException("ContainsAny supports only contains");
		}

		@Override
		public boolean remove(final Object arg0) {
			throw new UnsupportedOperationException("ContainsAny supports only contains");
		}

		@Override
		public boolean removeAll(final Collection<?> arg0) {
			throw new UnsupportedOperationException("ContainsAny supports only contains");
		}

		@Override
		public boolean retainAll(final Collection<?> arg0) {
			throw new UnsupportedOperationException("ContainsAny supports only contains");
		}

		@Override
		public int size() {
			throw new UnsupportedOperationException("ContainsAny supports only contains");
		}

		@Override
		public Object[] toArray() {
			throw new UnsupportedOperationException("ContainsAny supports only contains");
		}

		@Override
		public <T> T[] toArray(final T[] arg0) {
			throw new UnsupportedOperationException("ContainsAny supports only contains");
		}

	}
}
