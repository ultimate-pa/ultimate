package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;

public class tempVisitorSearch<L, S> implements IPartialOrderVisitor<L, S>{
	private final ArrayDeque<L> mLetterStack;
	private final ArrayDeque<S> mStateStack;
	private final ArrayList<L> mAcceptingTransitionSequence;
	private Word<L> mAcceptingWord;
	private final ArrayList<S> mAcceptingStateSequence;
	private final Function<S, Boolean> mIsGoalState;
	private S mStartState;
	
	public tempVisitorSearch(Function<S, Boolean> isGoalState) {
		mLetterStack = new ArrayDeque<>();
		mStateStack = new ArrayDeque<>();
		mAcceptingTransitionSequence = new ArrayList<>();
		mAcceptingStateSequence = new ArrayList<>();
		mAcceptingWord = new Word<>();
		mIsGoalState = isGoalState;
	}

	@Override
	public void discoverState(final S state) {

	}

	@Override
	public boolean discoverTransition(final S source, final L letter, final S target) {
		// push letter onto Stack
		mLetterStack.push(letter);
		mStateStack.push(target);
		return mIsGoalState.apply(target);
	}

	@Override
	public void backtrackState(final S state) {
		// pop state's list and remove letter leading to state from predecessor's list
		if (!state.equals(mStartState)) {
			mLetterStack.pop();
		}
		mStateStack.pop();
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
		
		S currentState = mStateStack.pop();
		mAcceptingStateSequence.add(0, currentState);
		L currentTransition;
		
		while (!mStateStack.isEmpty()) {
			currentTransition = mLetterStack.pop();
			mAcceptingTransitionSequence.add(0, currentTransition);
			currentState = mStateStack.pop();
			mAcceptingStateSequence.add(0, currentState);
		}
		//mAcceptingStateSequence.add(0, mStartState);

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
		mStateStack.push(state);
		return mIsGoalState.apply(state);
	}
}
