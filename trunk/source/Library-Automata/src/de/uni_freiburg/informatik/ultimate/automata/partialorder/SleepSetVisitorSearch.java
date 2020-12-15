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
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;

public class SleepSetVisitorSearch<L, S> implements IPartialOrderVisitor<L, S> {
	private final ArrayDeque<ArrayList<L>> mLetterStack;
	private final ArrayDeque<ArrayList<S>> mStateStack;
	private final ArrayList<L> mAcceptingTransitionSequence;
	private Word<L> mAcceptingWord;
	private final ArrayList<S> mAcceptingStateSequence;
	private final Function<S, Boolean> mIsGoalState;
	private S mStartState;
	
	public SleepSetVisitorSearch(Function<S, Boolean> isGoalState) {
		mLetterStack = new ArrayDeque<>();
		mStateStack = new ArrayDeque<>();
		mAcceptingTransitionSequence = new ArrayList<>();
		mAcceptingStateSequence = new ArrayList<>();
		mAcceptingWord = new Word<>();
		mIsGoalState = isGoalState;
	}

	@Override
	public void discoverState(final S state) {
		if (!state.equals(mStartState) && !mStateStack.peek().isEmpty()) {
			mLetterStack.push(new ArrayList<L>());
			mStateStack.push(new ArrayList<S>());
		}
	}

	@Override
	public boolean discoverTransition(final S source, final L letter, final S target) {
		// push letter onto Stack
		mLetterStack.peek().add(letter);
		mStateStack.peek().add(target);
		return mIsGoalState.apply(target);
	}

	@Override
	public void backtrackState(final S state) {
		// pop state's list and remove letter leading to state from predecessor's list
		if (mStateStack.peek().isEmpty()) {
			mLetterStack.pop();
			mStateStack.pop();
		}
		if (!mLetterStack.isEmpty()) {
			try {
				mLetterStack.peek().remove(0);
				mStateStack.peek().remove(0);
			} catch (IndexOutOfBoundsException e) {
				System.out.print("Size of LetterStack is: " + mLetterStack.size() + " and size of StateStack is: " + mStateStack.size());
				System.out.print("Size of LetterStack entry is: " + mLetterStack.peek().size() + " and size of StateStack entry is: " + mStateStack.peek().size());
			}
		}
	}
	
	public void delayState(final S state) {
		mLetterStack.peek().remove(mLetterStack.peek().size() - 1);
		mStateStack.peek().remove(mStateStack.peek().size() - 1);
	}

	public NestedRun<L, S> constructRun() {
		
		//problem: initial == final
		if (mIsGoalState.apply(mStartState)) {
			mAcceptingStateSequence.add(mStartState);
			final NestedWord<L> acceptingNestedWord = NestedWord.nestedWord(mAcceptingWord);
			return new NestedRun<>(acceptingNestedWord, mAcceptingStateSequence);
		}
		else if (mStateStack.isEmpty()) {
			return null;
		}
		
		ArrayList<L> currentTransitionList = mLetterStack.pop();
		L currentTransition = currentTransitionList.get(currentTransitionList.size() - 1);
		mAcceptingTransitionSequence.add(0, currentTransition);
		ArrayList<S> currentStateList = mStateStack.pop();
		S currentState = currentStateList.get(currentStateList.size() - 1);
		mAcceptingStateSequence.add(0, currentState);
		
		while (!mStateStack.isEmpty()) {
			currentTransitionList = mLetterStack.pop();
			currentTransition = currentTransitionList.get(0);
			mAcceptingTransitionSequence.add(0, currentTransition);
			currentStateList = mStateStack.pop();
			currentState = currentStateList.get(0);
			mAcceptingStateSequence.add(0, currentState);
		}
		mAcceptingStateSequence.add(0, mStartState);

		for (final L letter : mAcceptingTransitionSequence) {
			final Word<L> tempWord = new Word<>(letter);
			mAcceptingWord = mAcceptingWord.concatenate(tempWord);
		}
		final NestedWord<L> acceptingNestedWord = NestedWord.nestedWord(mAcceptingWord);
		System.out.print("Size of Word is: " + acceptingNestedWord.length() + " and size of Sequence is : " + mAcceptingStateSequence.size());
		return new NestedRun<>(acceptingNestedWord, mAcceptingStateSequence);
	}
	

	@Override
	public boolean addStartState(final S state) {
		mStartState = state;
		mLetterStack.push(new ArrayList<L>());
		mStateStack.push(new ArrayList<S>());
		return mIsGoalState.apply(state);
		// do nothing
	}
}
