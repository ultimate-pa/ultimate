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
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class SleepSetDelayReduction<L, S> extends UnaryNwaOperation<L, S, IStateFactory<S>>{
	
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final Set<S> mStartStateSet;
	private final HashMap<S, Set<L>> mHashMap;
	private final HashMap<S, Set<L>> mSleepSetMap;
	private final HashMap<S, Set<Set<L>>> mDelaySetMap;
	private final HashMap<S, ArrayList<Pair<S, L>>> mPreMap;
	private final Stack<S> mStack;
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
		mPreMap = new HashMap<S, ArrayList<Pair<S, L>>>();
		mStack = new Stack<S>();
		for (S startState : mStartStateSet) {
			mSleepSetMap.put(startState, Collections.<L>emptySet());
			mDelaySetMap.put(startState, Collections.<Set<L>>emptySet());
			mStack.push(startState);
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
		S currentState = mStack.firstElement();
		//accepting run reconstruction
		if (isGoalState(currentState)) {
			return constructRun(currentState);
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
				Set<Set<L>> succDelaySet = Collections.<Set<L>>emptySet();
				if(mStack.contains(succState)) {
					//mapping for accepting run reconstruction
					ArrayList<Pair<S, L>> preList = mPreMap.get(succState);
					preList.add(0, new Pair<S, L>(currentState, letterTransition));
					mPreMap.put(succState, preList);
					if (mDelaySetMap.get(succState) != null) {
						succDelaySet.addAll(mDelaySetMap.get(succState));
					}	
					succDelaySet.add(mSleepSetMap.get(succState));
					mDelaySetMap.put(succState, succDelaySet);
				}
				else {
					//mapping for accepting run reconstruction
					//mPreMap.put(succState, new Pair<S, L>(currentState, letterTransition));
					ArrayList<Pair<S, L>> preList = new ArrayList<Pair<S, L>>();
					preList.add(new Pair<S, L>(currentState, letterTransition));
					mPreMap.put(succState, preList);
					mDelaySetMap.put(succState, succDelaySet);
					mStack.push(succState);
					getAcceptingRun();
				}
				currentSleepSet.add(letterTransition);
				mSleepSetMap.put(currentState, currentSleepSet);
			}
		}
		mStack.pop();
		if (currentDelaySet.isEmpty() == false) {
			for (Set<L> sleepSet : currentDelaySet) {
				if (sleepSet.equals(currentSleepSet)) {
					currentDelaySet.remove(sleepSet);
				}
			}
			mDelaySetMap.put(currentState, currentDelaySet);
			mStack.push(currentState);
			getAcceptingRun();
		}
		return null;
	}
	
	private Boolean isGoalState(S state) {
		return mOperand.isFinal(state);
	}
	
	private NestedRun<L, S> constructRun(S state){
		if (mOperand.isInitial(state)) {
			return null;
		}
		S currentState = state;
		S preState = mPreMap.get(currentState).get(0).getFirst();
		L currentTransition = mPreMap.get(currentState).get(0).getSecond();
		while (currentState != null) {
			//do stuff
			mAcceptingStateSequence.add(currentState);
			if (currentTransition != null) {
				mAcceptingTransitionSequence.add(currentTransition);
			}
			mPreMap.get(currentState).remove(0);
			currentState = preState;
			currentTransition = mPreMap.get(currentState).get(0).getSecond();
			preState = mPreMap.get(currentState).get(0).getFirst();
		}
		Collections.reverse(mAcceptingStateSequence);
		Collections.reverse(mAcceptingTransitionSequence);
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
