package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.ArrayDeque;
import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;

public class DelayVisitorSearch<L, S> implements IPartialOrderVisitor<L,S> {
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final ArrayDeque<ArrayList<L>> mLetterStack;
	private final ArrayList<L> mAcceptingTransitionSequence;
	private final Word<L> mAcceptingWord;
	private final ArrayList<S> mAcceptingStateSequence;

	public DelayVisitorSearch(final INwaOutgoingLetterAndTransitionProvider<L, S> operand) {
		mOperand = operand;
		mLetterStack= new ArrayDeque<ArrayList<L>>();
		mAcceptingTransitionSequence = new ArrayList<>();
		mAcceptingStateSequence = new ArrayList<>();
		mAcceptingWord = new Word<>();
	}
	public void discoverState() {
		mLetterStack.push(new ArrayList<L>());
	}
	
	@Override
	public boolean discoverTransition(S source, L letter, S target) {
		//push letter onto Stack
		mLetterStack.peek().add(letter);
		return mOperand.isFinal(target);
	}

	@Override
	public void backtrackState(Object state) {
		//pop state's list and remove letter leading to state from predecessor's list
		mLetterStack.pop();
		mLetterStack.peek().remove(-1);	
	}
	
	public NestedRun<L, S> constructRun(ArrayDeque<S> stateStack) {
		S currentState = stateStack.pop();
		mAcceptingStateSequence.add(currentState);

		while (!stateStack.isEmpty()) {
			final ArrayList<L> currentTransitionList = mLetterStack.pop();
			final L currentTransition = currentTransitionList.get(-1);
			mAcceptingTransitionSequence.add(0, currentTransition);
			currentState = stateStack.pop();
			mAcceptingStateSequence.add(0, currentState);
		}
		for (final L letter : mAcceptingTransitionSequence) {
			final Word<L> tempWord = new Word<>(letter);
			mAcceptingWord.concatenate(tempWord);
		}
		NestedWord<L> acceptingNestedWord = NestedWord.nestedWord(mAcceptingWord);
		return new NestedRun<>(acceptingNestedWord, mAcceptingStateSequence);
	}
	
	public NestedWordAutomaton<L, S> getReductionAutomaton(){
		return null;
	}
	
	@Override
	public void addStartState(S state) {
		// do nothing
	}
}
