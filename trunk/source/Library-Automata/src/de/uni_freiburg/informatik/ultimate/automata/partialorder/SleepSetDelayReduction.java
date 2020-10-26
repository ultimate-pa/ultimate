package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

public class SleepSetDelayReduction<L, S> extends UnaryNwaOperation<L, S, IStateFactory<S>>{
	
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final S mStartState;
	private final HashMap<S, Set<OutgoingInternalTransition<L, S>>> mHashMap;
	private final HashMap<S, Set<OutgoingInternalTransition<L, S>>> mSleepSetMap;
	private final HashMap<S, Set<Set<OutgoingInternalTransition<L, S>>>> mDelaySetMap;
	private final Stack<S> mStack;
	private final NestedRun<L, S> mAcceptingRun;
	
	public SleepSetDelayReduction(final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final S startState,
			final IIndependenceRelation<S, L> independenceRelation,
			final ISleepSetOrder<S, L> sleepSetOrder,
			final AutomataLibraryServices services) {
		super(services);
		mOperand = operand;
		assert operand.getVpAlphabet().getCallAlphabet().isEmpty();
		assert operand.getVpAlphabet().getReturnAlphabet().isEmpty();
		mHashMap = new HashMap<S, Set<OutgoingInternalTransition<L, S>>>();
		mSleepSetMap = new HashMap<S, Set<OutgoingInternalTransition<L, S>>>();
		mSleepSetMap.put(startState, Collections.<OutgoingInternalTransition<L, S>>emptySet());
		mDelaySetMap = new HashMap<S, Set<Set<OutgoingInternalTransition<L, S>>>>();
		mDelaySetMap.put(startState, Collections.<Set<OutgoingInternalTransition<L, S>>>emptySet());
		mStack = new Stack<S>();
		mStartState = startState;
		mStack.push(startState);
		
		mAcceptingRun = getAcceptingRun();
		
	}

	private NestedRun<L,S> getAcceptingRun(){
		
		// TODO Insert pseudo code here
		S currentState = mStack.firstElement();
		Set<OutgoingInternalTransition<L, S>> successorTransitionSet = Collections.<OutgoingInternalTransition<L, S>>emptySet();
		Set<OutgoingInternalTransition<L, S>> currentSleepSet = mSleepSetMap.get(currentState);
		Set<Set<OutgoingInternalTransition<L, S>>> currentDelaySet = mDelaySetMap.get(currentState);
		
		if (mHashMap.get(currentState) == null){
			mHashMap.put(currentState, mSleepSetMap.get(currentState));
			for (OutgoingInternalTransition<L, S> transition : mOperand.internalSuccessors(currentState)) {
				if (currentSleepSet.contains(transition) == false) {
					successorTransitionSet.add(transition);		
				}	
			}
		}
		
		else {
			Set<OutgoingInternalTransition<L, S>> currentHash = mHashMap.get(currentState);
			for (OutgoingInternalTransition<L, S> transition : currentHash) {
				if (currentSleepSet.contains(transition) == false) {
					successorTransitionSet.add(transition);
				}
			}
			for (OutgoingInternalTransition<L, S> transition : currentSleepSet) {
				if (currentHash.contains(transition) == false) {
					currentSleepSet.remove(transition);
				}
			}
			mSleepSetMap.put(currentState, currentSleepSet);
			mHashMap.put(currentState, currentSleepSet);
		}
		
		for (OutgoingInternalTransition<L, S> transition : successorTransitionSet) {
			//do stuff
		}
		mStack.pop();
		if (currentDelaySet.isEmpty() == false) {
			for (Set<OutgoingInternalTransition<L, S>> sleepSet : currentDelaySet) {
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
