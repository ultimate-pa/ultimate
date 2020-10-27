package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

public class SleepSetDelayReduction<L, S> extends UnaryNwaOperation<L, S, IStateFactory<S>>{
	
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final Set<S> mStartStateSet;
	private final HashMap<S, Set<L>> mHashMap;
	private final HashMap<S, Set<L>> mSleepSetMap;
	private final HashMap<S, Set<Set<L>>> mDelaySetMap;
	private final Stack<S> mStateStack;
	private final Stack<L> mLetterStack;
	private final ISleepSetOrder<S, L> mOrder;
	private final IIndependenceRelation<S, L> mIndependenceRelation;
	private NestedRun<L, S> mAcceptingRun;
	private ArrayList<L> mAcceptingTransitionSequence;
	private Word<L> mAcceptingWord;
	private NestedWord<L> mAcceptingNestedWord;
	private ArrayList<S> mAcceptingStateSequence;
	
	public SleepSetDelayReduction(final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final IIndependenceRelation<S, L> independenceRelation,
			final ISleepSetOrder<S, L> sleepSetOrder,
			final AutomataLibraryServices services) {
		super(services);
		mOperand = operand;
		assert operand.getVpAlphabet().getCallAlphabet().isEmpty();
		assert operand.getVpAlphabet().getReturnAlphabet().isEmpty();
		mStartStateSet = CoreUtil.constructHashSet(operand.getInitialStates());
		assert (mStartStateSet.size() == 1);
		mHashMap = new HashMap<S, Set<L>>();
		mSleepSetMap = new HashMap<S, Set<L>>();
		mDelaySetMap = new HashMap<S, Set<Set<L>>>();
		mStateStack = new Stack<S>();
		mLetterStack = new Stack<L>();
		for (S startState : mStartStateSet) {
			mSleepSetMap.put(startState, Collections.<L>emptySet());
			mDelaySetMap.put(startState, Collections.<Set<L>>emptySet());
			mStateStack.push(startState);
		}
		mOrder = sleepSetOrder;
		mIndependenceRelation = independenceRelation;
		mAcceptingTransitionSequence = new ArrayList<L>();
		mAcceptingStateSequence = new ArrayList<S>();
		mAcceptingWord = new Word<L>();
		
		mAcceptingRun = getAcceptingRun();
		
	}

	private NestedRun<L,S> getAcceptingRun(){
		
		// TODO Insert pseudo code here
		S currentState = mStateStack.firstElement();
		//accepting run reconstruction
		if (isGoalState(currentState)) {
			return constructRun();
		}
		ArrayList<L> successorTransitionList = new ArrayList<L>();
		Set<L> currentSleepSet = mSleepSetMap.get(currentState);
		Set<Set<L>> currentDelaySet = mDelaySetMap.get(currentState);
		
		//state not visited yet
		if (mHashMap.get(currentState) == null){
			mHashMap.put(currentState, mSleepSetMap.get(currentState));
			for (OutgoingInternalTransition<L, S> transition : mOperand.internalSuccessors(currentState)) {
				if (currentSleepSet.contains(transition.getLetter()) == false) {
					successorTransitionList.add(transition.getLetter());
				}	
			}
		}
		//state already visited
		else {
			Set<L> currentHash = mHashMap.get(currentState);
			for (L letter : currentHash) {
				if (currentSleepSet.contains(letter) == false) {
					//following for loop is always executed exactly once, but needed to avoid a type mismatch
					for (OutgoingInternalTransition<L, S> transition : mOperand.internalSuccessors(currentState, letter)) {
						successorTransitionList.add(transition.getLetter());
					}
				}
			}
			for (L letter : currentSleepSet) {
				if (currentHash.contains(letter) == false) {
					currentSleepSet.remove(letter);
				}
			}
			mSleepSetMap.put(currentState, currentSleepSet);
			mHashMap.put(currentState, currentSleepSet);
		}
		//sort successorTransitionList according to the given order
		Comparator<L> order = mOrder.getOrder(currentState);
		successorTransitionList.sort(order);
		for (L letterTransition : successorTransitionList) {
			//following for loop is always executed exactly once, but needed to avoid a type mismatch
			for (OutgoingInternalTransition<L, S> currentTransition : mOperand.internalSuccessors(currentState, letterTransition)) {
				S succState = currentTransition.getSucc();
				Set<L> succSleepSet = Collections.<L>emptySet();
				for (L letterSleepSet : currentSleepSet) {
					if (mIndependenceRelation.contains(currentState, letterTransition, letterSleepSet)) {
						succSleepSet.add(letterSleepSet);
					}
				}
				mSleepSetMap.put(succState, succSleepSet);
				Set<Set<L>> succDelaySet = Collections.<Set<L>>emptySet();
				if(mStateStack.contains(succState)) {
					if (mDelaySetMap.get(succState) != null) {
						succDelaySet.addAll(mDelaySetMap.get(succState));
					}	
					succDelaySet.add(mSleepSetMap.get(succState));
					mDelaySetMap.put(succState, succDelaySet);
				}
				else {
					mDelaySetMap.put(succState, succDelaySet);
					mStateStack.push(succState);
					mLetterStack.push(letterTransition);
					getAcceptingRun();
				}
				currentSleepSet.add(letterTransition);
				mSleepSetMap.put(currentState, currentSleepSet);
			}
		}
		mStateStack.pop();
		if (currentDelaySet.isEmpty() == false) {
			for (Set<L> sleepSet : currentDelaySet) {
				if (sleepSet.equals(currentSleepSet)) {
					currentDelaySet.remove(sleepSet);
				}
			}
			mDelaySetMap.put(currentState, currentDelaySet);
			mStateStack.push(currentState);
			getAcceptingRun();
		}
		mLetterStack.pop();
		return null;
	}
	
	private Boolean isGoalState(S state) {
		return mOperand.isFinal(state);
	}
	
	private NestedRun<L, S> constructRun(){
		S currentState = mStateStack.pop();
		mAcceptingStateSequence.add(currentState);

		while(mStateStack.isEmpty() == false) {
			L currentTransition = mLetterStack.pop();
			mAcceptingTransitionSequence.add(0, currentTransition);
			currentState = mStateStack.pop();
			mAcceptingStateSequence.add(0, currentState);
			}
		for (L letter : mAcceptingTransitionSequence) {
			Word<L> tempWord = new Word<L>(letter);
			mAcceptingWord.concatenate(tempWord);
		}
		mAcceptingNestedWord = NestedWord.nestedWord(mAcceptingWord);
		mAcceptingRun = new NestedRun<L, S>(mAcceptingNestedWord, mAcceptingStateSequence);
		return mAcceptingRun;
	}
	
	@Override
	public Boolean getResult() {
		// TODO Auto-generated method stub
		return mAcceptingRun == null;
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<L, S> getOperand() {
		// TODO Auto-generated method stub
		return null;
	}

}
