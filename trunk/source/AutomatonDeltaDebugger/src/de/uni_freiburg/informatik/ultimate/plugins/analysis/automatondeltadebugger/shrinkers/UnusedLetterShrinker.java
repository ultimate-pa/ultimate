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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.utils.ELetterType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.utils.TypedLetter;

/**
 * Removes unused letters.
 * 
 * This shrinker removes only letters which do not occur on any transition.
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public class UnusedLetterShrinker<LETTER, STATE>
		extends AShrinker<TypedLetter<LETTER>, LETTER, STATE> {
	@Override
	public INestedWordAutomaton<LETTER, STATE>
			createAutomaton(List<TypedLetter<LETTER>> list) {
		// create alphabets
		final ListIterator<TypedLetter<LETTER>> it = list.listIterator();
		final Set<LETTER> internalAlphabet = unwrapLetters(it,
				mAutomaton.getAlphabet(), ELetterType.INTERNAL);
		final Set<LETTER> callAlphabet = unwrapLetters(it,
				mAutomaton.getCallAlphabet(), ELetterType.CALL);
		final Set<LETTER> returnAlphabet = unwrapLetters(it,
				mAutomaton.getReturnAlphabet(), ELetterType.RETURN);
		
		// create fresh automaton
		final INestedWordAutomaton<LETTER, STATE> automaton =
				mFactory.create(internalAlphabet, callAlphabet, returnAlphabet);
		
		// add original states
		mFactory.addStates(automaton, mAutomaton.getStates());
		
		// add transitions which still remain
		mFactory.addFilteredTransitions(automaton, mAutomaton);
		
		return automaton;
	}
	
	@Override
	public List<TypedLetter<LETTER>> extractList() {
		final HashSet<LETTER> internalsUsed = new HashSet<LETTER>();
		final HashSet<LETTER> callsUsed = new HashSet<LETTER>();
		final HashSet<LETTER> returnsUsed = new HashSet<LETTER>();
		
		// find used letters
		for (final STATE state : mAutomaton.getStates()) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans : mAutomaton
					.internalSuccessors(state)) {
				internalsUsed.add(trans.getLetter());
			}
			for (final OutgoingCallTransition<LETTER, STATE> trans : mAutomaton
					.callSuccessors(state)) {
				callsUsed.add(trans.getLetter());
			}
			for (final OutgoingReturnTransition<LETTER, STATE> trans : mAutomaton
					.returnSuccessors(state)) {
				returnsUsed.add(trans.getLetter());
			}
		}
		
		// wrap complement of present letters to include type information
		final ArrayList<TypedLetter<LETTER>> unused =
				new ArrayList<TypedLetter<LETTER>>();
		for (final LETTER letter : mAutomaton.getAlphabet()) {
			if (!internalsUsed.contains(letter)) {
				unused.add(
						new TypedLetter<LETTER>(letter, ELetterType.INTERNAL));
			}
		}
		for (final LETTER letter : mAutomaton.getCallAlphabet()) {
			if (!callsUsed.contains(letter)) {
				unused.add(new TypedLetter<LETTER>(letter, ELetterType.CALL));
			}
		}
		for (final LETTER letter : mAutomaton.getReturnAlphabet()) {
			if (!returnsUsed.contains(letter)) {
				unused.add(new TypedLetter<LETTER>(letter, ELetterType.RETURN));
			}
		}
		
		return unused;
	}
	
	/**
	 * Unwraps letters from the type wrapper list and creates the respective
	 * alphabet.
	 * 
	 * @param it iterator of type wrapper list
	 * @param originalAlphabet alphabet of original automaton
	 * @param letterType type of letter
	 * @return set of complementary letters
	 */
	private Set<LETTER> unwrapLetters(
			final ListIterator<TypedLetter<LETTER>> it,
			final Set<LETTER> originalAlphabet, final ELetterType letterType) {
		// find all letters which should be filtered
		final HashSet<LETTER> alphabetFilter = new HashSet<LETTER>();
		TypedLetter<LETTER> nextLetter;
		while (true) {
			if (it.hasNext()) {
				nextLetter = it.next();
				if (nextLetter.getType() != letterType) {
					// revert iterator
					it.previous();
					break;
				}
			} else {
				break;
			}
			
			final LETTER letter = nextLetter.getLetter();
			if (originalAlphabet.contains(letter)) {
				alphabetFilter.add(letter);
			}
		}
		
		// create the complement of the filtered letters
		final HashSet<LETTER> result = new HashSet<LETTER>();
		for (final LETTER letter : originalAlphabet) {
			if (!alphabetFilter.contains(letter)) {
				result.add(letter);
			}
		}
		return result;
	}
}
