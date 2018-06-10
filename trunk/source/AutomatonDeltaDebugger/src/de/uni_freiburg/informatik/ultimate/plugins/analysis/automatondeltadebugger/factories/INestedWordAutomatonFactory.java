/*
 * Copyright (C) 2015-2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automaton Delta Debugger.
 * 
 * The ULTIMATE Automaton Delta Debugger is free software: you can redistribute
 * it and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * The ULTIMATE Automaton Delta Debugger is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automaton Delta Debugger. If not, see
 * <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automaton Delta Debugger, or any covered work, by linking or
 * combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automaton Delta Debugger grant you additional
 * permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.factories;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.BridgeShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.utils.LetterType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.utils.TypedLetter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.utils.TypedTransition;

/**
 * Factory for {@link INestedWordAutomaton} objects.
 * <p>
 * NOTE: The automaton field is not updated during the shrinking process. Use it with caution.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public abstract class INestedWordAutomatonFactory<LETTER, STATE> {
	protected INestedWordAutomaton<LETTER, STATE> mAutomaton;

	/**
	 * @param automaton
	 *            Nested word automaton.
	 */
	public INestedWordAutomatonFactory(final INestedWordAutomaton<LETTER, STATE> automaton) {
		mAutomaton = automaton;
	}

	/**
	 * Create new automaton using alphabets of old automaton.
	 * 
	 * @param automaton
	 *            automaton to use the alphabet of
	 * @return new {@link INestedWordAutomaton} object
	 */
	public INestedWordAutomaton<LETTER, STATE> create(final INestedWordAutomaton<LETTER, STATE> automaton) {
		return create(automaton.getVpAlphabet().getInternalAlphabet(), automaton.getVpAlphabet().getCallAlphabet(),
				automaton.getVpAlphabet().getReturnAlphabet());
	}

	/**
	 * Create new automaton using given alphabets or those of old automaton if {@code null}.
	 * 
	 * @param internalAlphabet
	 *            internal alphabet, null uses original one
	 * @param callAlphabet
	 *            call alphabet, null uses original one
	 * @param returnAlphabet
	 *            return alphabet, null uses original one
	 * @return new {@link INestedWordAutomaton} object with specified alphabets
	 */
	public INestedWordAutomaton<LETTER, STATE> create(final Set<LETTER> internalAlphabet,
			final Set<LETTER> callAlphabet, final Set<LETTER> returnAlphabet) {
		final Set<LETTER> internalAlphabetRes =
				(internalAlphabet == null) ? mAutomaton.getVpAlphabet().getInternalAlphabet() : internalAlphabet;
		final Set<LETTER> callAlphabetRes =
				(callAlphabet == null) ? mAutomaton.getVpAlphabet().getCallAlphabet() : callAlphabet;
		final Set<LETTER> returnAlphabetRes =
				(returnAlphabet == null) ? mAutomaton.getVpAlphabet().getReturnAlphabet() : returnAlphabet;

		return createWithAlphabets(internalAlphabetRes, callAlphabetRes, returnAlphabetRes);
	}

	/**
	 * Create new automaton using given alphabets.
	 * 
	 * @param internalAlphabet
	 *            internal alphabet
	 * @param callAlphabet
	 *            call alphabet
	 * @param returnAlphabet
	 *            return alphabet
	 * @return new {@link INestedWordAutomaton} object with specified alphabets
	 */
	protected abstract INestedWordAutomaton<LETTER, STATE> createWithAlphabets(Set<LETTER> internalAlphabet,
			Set<LETTER> callAlphabet, Set<LETTER> returnAlphabet);

	/**
	 * This method assumes that the passed state is present of the original automaton.
	 * 
	 * @param automaton
	 *            automaton
	 * @param state
	 *            new state to add
	 */
	public void addState(final INestedWordAutomaton<LETTER, STATE> automaton, final STATE state) {
		addState(automaton, state, mAutomaton.isInitial(state), mAutomaton.isFinal(state));
	}

	/**
	 * Adds a state with the initial and final status of the old automaton.
	 * 
	 * @param automaton
	 *            automaton
	 * @param state
	 *            new state to add
	 * @param isInitial
	 *            true iff state is initial
	 * @param isFinal
	 *            true iff state is final
	 */
	public abstract void addState(INestedWordAutomaton<LETTER, STATE> automaton, STATE state, boolean isInitial,
			boolean isFinal);

	/**
	 * Adds an internal transition.
	 * 
	 * @param automaton
	 *            automaton
	 * @param pred
	 *            predecessor state
	 * @param letter
	 *            letter
	 * @param succ
	 *            successor state
	 */
	public abstract void addInternalTransition(INestedWordAutomaton<LETTER, STATE> automaton, STATE pred, LETTER letter,
			STATE succ);

	/**
	 * Adds call transition.
	 * 
	 * @param automaton
	 *            automaton
	 * @param pred
	 *            predecessor state
	 * @param letter
	 *            letter
	 * @param succ
	 *            successor state
	 */
	public abstract void addCallTransition(INestedWordAutomaton<LETTER, STATE> automaton, STATE pred, LETTER letter,
			STATE succ);

	/**
	 * Adds a return transition.
	 * 
	 * @param automaton
	 *            automaton
	 * @param pred
	 *            linear predecessor state
	 * @param hier
	 *            hierarchical predecessor state
	 * @param letter
	 *            letter
	 * @param succ
	 *            successor state
	 */
	public abstract void addReturnTransition(INestedWordAutomaton<LETTER, STATE> automaton, STATE pred, STATE hier,
			LETTER letter, STATE succ);

	/**
	 * Adds a collection of states.
	 * <p>
	 * A convenient loop which calls {@link #addState(INestedWordAutomaton, Object)} in the background.
	 * 
	 * @param automaton
	 *            automaton
	 * @param states
	 *            new states to add
	 */
	public void addStates(final INestedWordAutomaton<LETTER, STATE> automaton, final Collection<STATE> states) {
		for (final STATE state : states) {
			addState(automaton, state);
		}
	}

	/**
	 * Adds a collection of internal transitions.
	 * <p>
	 * A convenient loop which calls {@link #addInternalTransition(INestedWordAutomaton, Object, Object, Object)} in the
	 * background.
	 * 
	 * @param automaton
	 *            automaton
	 * @param transitions
	 *            internal transitions
	 */
	public void addInternalTransitions(final INestedWordAutomaton<LETTER, STATE> automaton,
			final Collection<TypedTransition<LETTER, STATE>> transitions) {
		for (final TypedTransition<LETTER, STATE> trans : transitions) {
			assert trans.getLetter().getType() == LetterType.INTERNAL : "No internal transition.";
			addInternalTransition(automaton, trans.getPred(), trans.getLetter().getLetter(), trans.getSucc());
		}
	}

	/**
	 * Adds a collection of call transitions.
	 * <p>
	 * A convenient loop which calls {@link #addCallTransition(INestedWordAutomaton, Object, Object, Object)} in the
	 * background.
	 * 
	 * @param automaton
	 *            automaton
	 * @param transitions
	 *            internal transitions
	 */
	public void addCallTransitions(final INestedWordAutomaton<LETTER, STATE> automaton,
			final Collection<TypedTransition<LETTER, STATE>> transitions) {
		for (final TypedTransition<LETTER, STATE> trans : transitions) {
			assert trans.getLetter().getType() == LetterType.CALL : "No call transition.";
			addCallTransition(automaton, trans.getPred(), trans.getLetter().getLetter(), trans.getSucc());
		}
	}

	/**
	 * Adds a collection of return transitions.
	 * <p>
	 * A convenient loop which calls {@link #addReturnTransition(INestedWordAutomaton, Object, Object, Object, Object)}
	 * in the background.
	 * 
	 * @param automaton
	 *            automaton
	 * @param transitions
	 *            return transitions
	 */
	public void addReturnTransitions(final INestedWordAutomaton<LETTER, STATE> automaton,
			final Collection<TypedTransition<LETTER, STATE>> transitions) {
		for (final TypedTransition<LETTER, STATE> trans : transitions) {
			assert trans.getLetter().getType() == LetterType.RETURN : "No return transition.";
			addReturnTransition(automaton, trans.getPred(), trans.getHier(), trans.getLetter().getLetter(),
					trans.getSucc());
		}
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @return all internal transitions
	 */
	public Set<TypedTransition<LETTER, STATE>>
			getInternalTransitions(final INestedWordAutomaton<LETTER, STATE> automaton) {
		final Set<TypedTransition<LETTER, STATE>> transitions = new HashSet<>();
		for (final STATE state : automaton.getStates()) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans : automaton.internalSuccessors(state)) {
				transitions.add(new TypedTransition<>(state, trans.getSucc(), null,
						new TypedLetter<>(trans.getLetter(), LetterType.INTERNAL)));
			}
		}
		return transitions;
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @return all call transitions
	 */
	public Set<TypedTransition<LETTER, STATE>> getCallTransitions(final INestedWordAutomaton<LETTER, STATE> automaton) {
		final Set<TypedTransition<LETTER, STATE>> transitions = new HashSet<>();
		for (final STATE state : automaton.getStates()) {
			for (final OutgoingCallTransition<LETTER, STATE> trans : automaton.callSuccessors(state)) {
				transitions.add(new TypedTransition<>(state, trans.getSucc(), null,
						new TypedLetter<>(trans.getLetter(), LetterType.CALL)));
			}
		}
		return transitions;
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @return all return transitions
	 */
	public Set<TypedTransition<LETTER, STATE>>
			getReturnTransitions(final INestedWordAutomaton<LETTER, STATE> automaton) {
		final Set<TypedTransition<LETTER, STATE>> transitions = new HashSet<>();
		for (final STATE state : automaton.getStates()) {
			for (final OutgoingReturnTransition<LETTER, STATE> trans : automaton.returnSuccessors(state)) {
				transitions.add(new TypedTransition<>(state, trans.getSucc(), trans.getHierPred(),
						new TypedLetter<>(trans.getLetter(), LetterType.RETURN)));
			}
		}
		return transitions;
	}

	/**
	 * Adds original internal transitions filtered by current states.
	 * 
	 * @param automatonTo
	 *            automaton to add the transitions to
	 * @param automatonFrom
	 *            automaton to take the transitions from
	 */
	public void addFilteredInternalTransitions(final INestedWordAutomaton<LETTER, STATE> automatonTo,
			final INestedWordAutomaton<LETTER, STATE> automatonFrom) {
		final Set<STATE> remainingStates = automatonTo.getStates();
		for (final STATE state : remainingStates) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans : automatonFrom.internalSuccessors(state)) {
				final STATE succ = trans.getSucc();
				if (remainingStates.contains(succ)) {
					addInternalTransition(automatonTo, state, trans.getLetter(), succ);
				}
			}
		}
	}

	/**
	 * Adds original call transitions filtered by current states.
	 * 
	 * @param automatonTo
	 *            automaton to add the transitions to
	 * @param automatonFrom
	 *            automaton to take the transitions from
	 */
	public void addFilteredCallTransitions(final INestedWordAutomaton<LETTER, STATE> automatonTo,
			final INestedWordAutomaton<LETTER, STATE> automatonFrom) {
		final Set<STATE> remainingStates = automatonTo.getStates();
		for (final STATE state : remainingStates) {
			for (final OutgoingCallTransition<LETTER, STATE> trans : automatonFrom.callSuccessors(state)) {
				final STATE succ = trans.getSucc();
				if (remainingStates.contains(succ)) {
					addCallTransition(automatonTo, state, trans.getLetter(), succ);
				}
			}
		}
	}

	/**
	 * Adds original return transitions filtered by current states.
	 * 
	 * @param automatonTo
	 *            automaton to add the transitions to
	 * @param automatonFrom
	 *            automaton to take the transitions from
	 */
	public void addFilteredReturnTransitions(final INestedWordAutomaton<LETTER, STATE> automatonTo,
			final INestedWordAutomaton<LETTER, STATE> automatonFrom) {
		final Set<STATE> remainingStates = automatonTo.getStates();
		for (final STATE state : remainingStates) {
			for (final OutgoingReturnTransition<LETTER, STATE> trans : automatonFrom.returnSuccessors(state)) {
				final STATE succ = trans.getSucc();
				final STATE hier = trans.getHierPred();
				if ((remainingStates.contains(succ)) && (remainingStates.contains(hier))) {
					addReturnTransition(automatonTo, state, hier, trans.getLetter(), succ);
				}
			}
		}
	}

	/**
	 * Adds original transitions filtered by current states.
	 * 
	 * @param automatonTo
	 *            automaton to add the transitions to
	 * @param automatonFrom
	 *            automaton to take the transitions from
	 */
	public void addFilteredTransitions(final INestedWordAutomaton<LETTER, STATE> automatonTo,
			final INestedWordAutomaton<LETTER, STATE> automatonFrom) {
		addFilteredInternalTransitions(automatonTo, automatonFrom);
		addFilteredCallTransitions(automatonTo, automatonFrom);
		addFilteredReturnTransitions(automatonTo, automatonFrom);
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}

	/**
	 * Setter for the backing automaton.
	 * <p>
	 * USE WITH CAUTION!<br>
	 * This might mess up all internal logic. Should only be used by {@link BridgeShrinker}s.
	 * 
	 * @param automaton
	 *            new automaton
	 */
	public void setAutomaton(final INestedWordAutomaton<LETTER, STATE> automaton) {
		mAutomaton = automaton;
	}
}
