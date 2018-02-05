/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization;

import java.io.PrintWriter;
import java.util.Collection;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.GeneralAutomatonPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IEpsilonNestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;

/**
 * Prints an {@link INestedWordAutomaton}.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public abstract class NwaWriter<LETTER, STATE> extends GeneralAutomatonPrinter {
	private final INestedWordAutomaton<LETTER, STATE> mNwa;
	private final Map<LETTER, String> mInternalAlphabet;
	private final Map<LETTER, String> mCallAlphabet;
	private final Map<LETTER, String> mReturnAlphabet;
	private final Map<STATE, String> mStateMapping;

	/**
	 * @param writer
	 *            Print writer.
	 * @param name
	 *            automaton name
	 * @param nwa
	 *            nested word automaton
	 */
	@SuppressWarnings("squid:S1699")
	public NwaWriter(final PrintWriter writer, final String name, final INestedWordAutomaton<LETTER, STATE> nwa) {
		super(writer);
		mNwa = nwa;
		mInternalAlphabet = getAlphabetMapping(mNwa.getVpAlphabet().getInternalAlphabet(), 'a');
		mCallAlphabet = getAlphabetMapping(mNwa.getVpAlphabet().getCallAlphabet(), 'c');
		mReturnAlphabet = getAlphabetMapping(mNwa.getVpAlphabet().getReturnAlphabet(), 'r');
		mStateMapping = getStateMapping(mNwa.getStates());

		final boolean hasEpsilonTransitions = (mNwa instanceof IEpsilonNestedWordAutomaton);
		if (hasEpsilonTransitions) {
			// automata script format for NestedWordAutomaton
			print("EpsilonNestedWordAutomaton ");
			print(name);
			printAutomatonPrefix();
			printAlphabets();
			printStates();
			printInitialStates(mNwa.getInitialStates());
			printFinalStates(mNwa.getStates());
			printCallTransitions(mNwa.getStates());
			printTransitionListSeparator();
			printInternalTransitions(mNwa.getStates());
			printTransitionListSeparator();
			printReturnTransitions(mNwa.getStates());
			printTransitionListSeparator();
			printEpsilonTransitions(mNwa.getStates());
			printLastTransitionLineSeparator();
			printAutomatonSuffix();
		} else {
			final boolean isFiniteAutomaton = mCallAlphabet.isEmpty() && mReturnAlphabet.isEmpty();
			if (isFiniteAutomaton) {
				// automata script format for FiniteAutomaton
				print("FiniteAutomaton ");
				print(name);
				printAutomatonPrefix();
				printAlphabetOfFiniteAutomaton();
				printStates();
				printInitialStates(mNwa.getInitialStates());
				printFinalStates(mNwa.getStates());
				printTransitionsOfFiniteAutomaton(mNwa.getStates());
				printLastTransitionLineSeparator();
				printAutomatonSuffix();
			} else {
				// automata script format for NestedWordAutomaton
				print("NestedWordAutomaton ");
				print(name);
				printAutomatonPrefix();
				printAlphabets();
				printStates();
				printInitialStates(mNwa.getInitialStates());
				printFinalStates(mNwa.getStates());
				printCallTransitions(mNwa.getStates());
				printTransitionListSeparator();
				printInternalTransitions(mNwa.getStates());
				printTransitionListSeparator();
				printReturnTransitions(mNwa.getStates());
				printLastTransitionLineSeparator();
				printAutomatonSuffix();
			}
		}
		finish();
	}

	/**
	 * Constructs the new alphabet.
	 *
	 * @param alphabet
	 *            old alphabet
	 * @param symbol
	 *            default symbol
	 * @return mapping (old alphabet -> new alphabet)
	 */
	protected abstract Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet, final char symbol);

	/**
	 * Constructs the new states.
	 *
	 * @param states
	 *            old states
	 * @return new states
	 */
	protected abstract Map<STATE, String> getStateMapping(final Collection<STATE> states);

	private void printAlphabets() {
		printCollectionPrefix("callAlphabet");
		printValues(mCallAlphabet);
		printCollectionSuffix();

		printCollectionPrefix("internalAlphabet");
		printValues(mInternalAlphabet);
		printCollectionSuffix();

		printCollectionPrefix("returnAlphabet");
		printValues(mReturnAlphabet);
		printCollectionSuffix();
	}

	private void printAlphabetOfFiniteAutomaton() {
		printCollectionPrefix("alphabet");
		printValues(mInternalAlphabet);
		printCollectionSuffix();
	}

	private void printStates() {
		printCollectionPrefix("states");
		printValues(mStateMapping);
		printCollectionSuffix();
	}

	private void printInitialStates(final Collection<STATE> initialStates) {
		printCollectionPrefix("initialStates");
		for (final STATE state : initialStates) {
			printElement(mStateMapping.get(state));
		}
		printCollectionSuffix();
	}

	private void printFinalStates(final Collection<STATE> allStates) {
		printCollectionPrefix("finalStates");
		for (final STATE state : allStates) {
			if (mNwa.isFinal(state)) {
				printElement(mStateMapping.get(state));
			}
		}
		printCollectionSuffix();
	}

	private void printTransitionsOfFiniteAutomaton(final Collection<STATE> allStates) {
		printlnCollectionPrefix("transitions");
		for (final STATE state : allStates) {
			for (final OutgoingInternalTransition<LETTER, STATE> internalTrans : mNwa.internalSuccessors(state)) {
				printOneTransitionPrefix();
				print(mStateMapping.get(state));
				print(' ');
				print(mInternalAlphabet.get(internalTrans.getLetter()));
				print(' ');
				print(mStateMapping.get(internalTrans.getSucc()));
				printOneTransitionSuffix();
			}
		}
		printTransitionsSuffix();
	}

	private void printCallTransitions(final Collection<STATE> allStates) {
		printlnCollectionPrefix("callTransitions");
		for (final STATE state : allStates) {
			for (final OutgoingCallTransition<LETTER, STATE> callTrans : mNwa.callSuccessors(state)) {
				printOneTransitionPrefix();
				print(mStateMapping.get(state));
				print(' ');
				print(mCallAlphabet.get(callTrans.getLetter()));
				print(' ');
				print(mStateMapping.get(callTrans.getSucc()));
				printOneTransitionSuffix();
			}
		}
		printTransitionsSuffix();
	}

	private void printInternalTransitions(final Collection<STATE> allStates) {
		printlnCollectionPrefix("internalTransitions");
		for (final STATE state : allStates) {
			for (final OutgoingInternalTransition<LETTER, STATE> internalTrans : mNwa.internalSuccessors(state)) {
				printOneTransitionPrefix();
				print(mStateMapping.get(state));
				print(' ');
				print(mInternalAlphabet.get(internalTrans.getLetter()));
				print(' ');
				print(mStateMapping.get(internalTrans.getSucc()));
				printOneTransitionSuffix();
			}
		}
		printTransitionsSuffix();
	}

	private void printReturnTransitions(final Collection<STATE> allStates) {
		printlnCollectionPrefix("returnTransitions");
		for (final STATE state : allStates) {
			for (final OutgoingReturnTransition<LETTER, STATE> returnTrans : mNwa.returnSuccessors(state)) {
				printOneTransitionPrefix();
				print(mStateMapping.get(state));
				print(' ');
				print(mStateMapping.get(returnTrans.getHierPred()));
				print(' ');
				print(mReturnAlphabet.get(returnTrans.getLetter()));
				print(' ');
				print(mStateMapping.get(returnTrans.getSucc()));
				printOneTransitionSuffix();
			}
		}
		printTransitionsSuffix();
	}

	private void printEpsilonTransitions(final Collection<STATE> allStates) {
		printlnCollectionPrefix("epsilonTransitions");
		for (final STATE state : allStates) {
			for (final STATE succ : ((IEpsilonNestedWordAutomaton<LETTER, STATE>) mNwa).epsilonSuccessors(state)) {
				printOneTransitionPrefix();
				print(mStateMapping.get(state));
				print(' ');
				print(mStateMapping.get(succ));
				printOneTransitionSuffix();
			}
		}
		printTransitionsSuffix();
	}
}
