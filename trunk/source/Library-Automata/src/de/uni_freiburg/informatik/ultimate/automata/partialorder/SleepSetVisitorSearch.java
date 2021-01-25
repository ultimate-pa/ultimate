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
import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;

public class SleepSetVisitorSearch<L, S> implements IPartialOrderVisitor<L, S> {
	private Set<S> mDeadEndSet;
	private  ArrayDeque<ArrayList<L>> mLetterStack;
	private  ArrayDeque<ArrayList<S>> mStateStack;
	private  ArrayList<L> mAcceptingTransitionSequence;
	private Word<L> mAcceptingWord;
	private  ArrayList<S> mAcceptingStateSequence;
	private final Function<S, Boolean> mIsGoalState;
	private final Function<S, Boolean> mIsHopelessState;
	private S mStartState;
	
	public SleepSetVisitorSearch(Function<S, Boolean> isGoalState, Function<S, Boolean> isHopelessState) {
		mDeadEndSet = new HashSet<S>();
		mLetterStack = new ArrayDeque<>();
		mStateStack = new ArrayDeque<>();
		mAcceptingTransitionSequence = new ArrayList<>();
		mAcceptingStateSequence = new ArrayList<>();
		mAcceptingWord = new Word<>();
		mIsGoalState = isGoalState;
		mIsHopelessState = isHopelessState;
	}

	@Override
	public boolean discoverState(final S state) {
		if (!state.equals(mStartState) && !mStateStack.peek().isEmpty()) {
			mLetterStack.push(new ArrayList<L>());
			mStateStack.push(new ArrayList<S>());
		}
		return isDeadEndState(state) || mIsHopelessState.apply(state);
	}

	@Override
	public boolean discoverTransition(final S source, final L letter, final S target) {
		// push letter onto Stack
		mLetterStack.peek().add(letter);
		mStateStack.peek().add(target);
		return mIsGoalState.apply(target);
	}

	@Override
	public void backtrackState(final S state, final boolean loop) {
		// pop state's list and remove letter leading to state from predecessor's list
		if (!loop) {
			mDeadEndSet.add(state);
		}
		//mDeadEndSet.add(state); //disable this line to disable DeadEndDetection
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
	
	@Override
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
		reset();
		mStartState = state;
		mLetterStack.push(new ArrayList<L>());
		mStateStack.push(new ArrayList<S>());
		return mIsGoalState.apply(state);
		// do nothing
	}
	
	private void reset() {
		mLetterStack = new ArrayDeque<>();
		mStateStack = new ArrayDeque<>();
		mAcceptingTransitionSequence = new ArrayList<>();
		mAcceptingStateSequence = new ArrayList<>();
		mAcceptingWord = new Word<>();
	}
	
	public boolean isDeadEndState(S state) {
	// TODO (Dominik 2021-01-24) Consider moving dead-end optimization to subclass
		return mDeadEndSet.contains(state);
	}
	
	public void addDeadEndState(S state) {
		mDeadEndSet.add(state);
	}
}
