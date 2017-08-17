package operation.emptiness;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import automata.IBuchi;
import automata.IState;
import util.IPair;
import util.IntIterator;
import util.IntSet;
import util.IntStack;
import util.Timer;
import util.UtilIntSet;

public class BuchiIsEmptyTarjanOriginal implements BuchiIsEmpty {
	
	private final IBuchi mBuchi;
	private int mIndex;
	private final IntStack mStateStack;
	private final Map<Integer,Integer> mIndexMap ;
	private final Map<Integer,Integer> mLowlinkMap;

	private final long TIME_LIMIT;
	private final Timer mTimer;
	private Boolean mIsEmpty = true;
	
	public BuchiIsEmptyTarjanOriginal(IBuchi buchi, int timeLimit) {
		
		this.mBuchi = buchi;
		this.TIME_LIMIT  = timeLimit;
		this.mStateStack = new IntStack();
		this.mLowlinkMap = new HashMap<Integer,Integer>();
		this.mIndexMap   = new HashMap<Integer,Integer>();

		this.mTimer = new Timer();
		mTimer.start();
		explore();
	}

	private void explore() {
		// TODO Auto-generated method stub
		mIndex = 0;
		IntIterator iter = mBuchi.getInitialStates().iterator();
		while(iter.hasNext()) {
			int n = iter.next();
			if(!mIndexMap.containsKey(n) && !terminate()){
				strongConnect(n);
				if(mIsEmpty == null || mIsEmpty.booleanValue() == false) return;
			}
		}
	}
	
	private boolean terminate() {
		if(mTimer.tick() > TIME_LIMIT) 
			return true;
		return false;
	}

	private void strongConnect(int v) {
		
		if(terminate()) {
			mIsEmpty = null;
			return ;
		}
		// TODO Auto-generated method stub
		mStateStack.push(v);;
		mIndexMap.put(v, mIndex);
		mLowlinkMap.put(v, mIndex);
		++ mIndex;			
		
		IState state = mBuchi.getState(v);
		//TODO only get enabled letters
		for(int letter = 0; letter < mBuchi.getAlphabetSize(); letter ++) {
			IntSet succs = state.getSuccessors(letter);
			IntIterator iter = succs.iterator();
			while(iter.hasNext()) {
				int succ = iter.next();
				if(! mIndexMap.containsKey(succ)) {
					strongConnect(succ);
					if(mIsEmpty == null || mIsEmpty.booleanValue() == false) return;
                    mLowlinkMap.put(v, Math.min(mLowlinkMap.get(v), mLowlinkMap.get(succ)));					
				}else if(mStateStack.contains(succ)) {
				    mLowlinkMap.put(v, Math.min(mLowlinkMap.get(v), mIndexMap.get(succ)));					
				}
			}
		}
		
		if(mLowlinkMap.get(v).intValue() == mIndexMap.get(v).intValue()){
			IntSet scc = UtilIntSet.newIntSet();
			while(! mStateStack.isEmpty()){
				int t = mStateStack.pop();
				scc.set(t);
				if(t == v)
					break;
			}

			boolean hasAcc = mBuchi.getAcceptance().isAccepted(scc);
			
			if(scc.cardinality() == 1 // only has a single state
					&& hasAcc        // it is an accepting states
					) {
				IState s = mBuchi.getState(v);
				boolean hasSelfLoop = false;
				for(Integer letter : s.getEnabledLetters()) {
					if(s.getSuccessors(letter).get(v)) hasSelfLoop = true;
				}
				if(!hasSelfLoop) hasAcc = false;
			}
							
			if(hasAcc) {
				mIsEmpty = false;
			}
		}
	}

	@Override
	public Boolean isEmpty() {
		// TODO Auto-generated method stub
		return mIsEmpty;
	}

	@Override
	public IPair<List<Integer>, List<Integer>> getAcceptingWord() {
		// TODO Auto-generated method stub
		return null;
	}
			

}
