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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.ArrayDeque;
import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;

public class SleepSetVisitorSearch<L, S> implements IPartialOrderVisitor<L,S> {
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final ArrayDeque<ArrayList<L>> mLetterStack;
	private final ArrayDeque<ArrayList<S>> mStateStack;
	private final ArrayList<L> mAcceptingTransitionSequence;
	private final Word<L> mAcceptingWord;
	private final ArrayList<S> mAcceptingStateSequence;

	public SleepSetVisitorSearch(final INwaOutgoingLetterAndTransitionProvider<L, S> operand) {
		mOperand = operand;
		mLetterStack= new ArrayDeque<ArrayList<L>>();
		mStateStack= new ArrayDeque<ArrayList<S>>();
		mAcceptingTransitionSequence = new ArrayList<>();
		mAcceptingStateSequence = new ArrayList<>();
		mAcceptingWord = new Word<>();
	}
	@Override
	public void discoverState() {
		mLetterStack.push(new ArrayList<L>());
		mStateStack.push(new ArrayList<S>());
	}
	
	@Override
	public boolean discoverTransition(S source, L letter, S target) {
		//push letter onto Stack
		mLetterStack.peek().add(letter);
		mStateStack.peek().add(target);
		return mOperand.isFinal(target);
	}

	@Override
	public void backtrackState(Object state) {
		//pop state's list and remove letter leading to state from predecessor's list
		mLetterStack.pop();
		mLetterStack.peek().remove(0);
		mStateStack.pop();
		mStateStack.peek().remove(0);
	}
	
	public NestedRun<L, S> constructRun() {
		ArrayList<S> currentStateList = mStateStack.pop();
		S currentState = currentStateList.get(-1);
		mAcceptingStateSequence.add(currentState);
		ArrayList<L> currentTransitionList;
		L currentTransition;
		if (!mStateStack.isEmpty()) {
			currentTransitionList = mLetterStack.pop();
			currentTransition = currentTransitionList.get(-1);
			mAcceptingTransitionSequence.add(0, currentTransition);
			currentTransitionList = mLetterStack.pop();
			currentTransition = currentTransitionList.get(0);
			mAcceptingTransitionSequence.add(0, currentTransition);
		}
		
		while (!mStateStack.isEmpty()) {
			currentTransitionList = mLetterStack.pop();
			currentTransition = currentTransitionList.get(0);
			mAcceptingTransitionSequence.add(0, currentTransition);
			currentStateList = mStateStack.pop();
			currentState = currentStateList.get(0);
			mAcceptingStateSequence.add(0, currentState);
		}
		
		for (final L letter : mAcceptingTransitionSequence) {
			final Word<L> tempWord = new Word<>(letter);
			mAcceptingWord.concatenate(tempWord);
		}
		NestedWord<L> acceptingNestedWord = NestedWord.nestedWord(mAcceptingWord);
		return new NestedRun<>(acceptingNestedWord, mAcceptingStateSequence);
	}
	
	@Override
	public void addStartState(S state) {
		// do nothing
	}
}
