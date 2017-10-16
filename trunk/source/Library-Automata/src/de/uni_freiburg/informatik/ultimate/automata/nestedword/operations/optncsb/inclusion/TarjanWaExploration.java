package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.Options;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IBuchiWa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IStateWa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.MarkedIntStack;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;
import gnu.trove.list.TIntList;
import gnu.trove.list.array.TIntArrayList;
import gnu.trove.map.TIntIntMap;
import gnu.trove.map.hash.TIntIntHashMap;


public class TarjanWaExploration implements EmptinessExploration {
	
	private int mIndex;
	private final MarkedIntStack mStateStack;
	private final TIntIntMap mIndexMap ;
	private final TIntIntMap mLowlinkMap;
	private TIntList mSCC;
	private Boolean mIsEmpty;
	private final IBuchiWa mBuchi;
	
	public TarjanWaExploration(IBuchiWa buchi) {
		
		mBuchi = buchi;
		mStateStack = new MarkedIntStack(false);
		mIndexMap = new TIntIntHashMap();
		mLowlinkMap = new TIntIntHashMap();
		
		mIsEmpty = true;
		tarjan();
	}
	
	@Override
	public Boolean isEmpty() {
		return mIsEmpty;
	}

	private void tarjan() {
		mIndex = 0;
		for (final int init : mBuchi.getInitialStates().iterable()) {
			if (!mIndexMap.containsKey(init)) {
				strongConnect(init);
			}
		}
	}

	private void strongConnect(int v) {
		
		mStateStack.push(v);
		mIndexMap.put(v, mIndex);
		mLowlinkMap.put(v, mIndex);
		
		++ mIndex;	
		
		IStateWa state = mBuchi.getState(v);
		for(int letter = 0; letter < mBuchi.getAlphabetSize(); letter ++) {
			IntSet succs = state.getSuccessors(letter);
			for(final Integer succ : succs.iterable()) {
				if(! mIndexMap.containsKey(succ)) {
					strongConnect(succ); // did not visit succ before
                    mLowlinkMap.put(v, Math.min(mLowlinkMap.get(v), mLowlinkMap.get(succ)));					
				}else if(mStateStack.contains(succ)) {
				    mLowlinkMap.put(v, Math.min(mLowlinkMap.get(v), mIndexMap.get(succ)));					
				}
			}
		}
		
		// found one strongly connected component
		if(mLowlinkMap.get(v) == mIndexMap.get(v)){
			
			IntSet sccSet = UtilIntSet.newIntSet();
			TIntList sccList = new TIntArrayList();
			
			while(! mStateStack.empty()){
				int t = mStateStack.pop();
				sccSet.set(t);
				sccList.add(t);
				if(t == v)
					break;
			}

			boolean hasAcc = mBuchi.getAcceptance().isAccepted(sccSet);
			if(Options.verbose) System.out.println("hasAcc: " + hasAcc + "," + sccSet);
			
			if(sccSet.cardinality() == 1 // only has a single state
					&& hasAcc            // it is an accepting states
					) {
				boolean hasSelfLoop = false;
				for(Integer letter : state.getEnabledLetters()) {
					if(state.getSuccessors(letter).get(v)) hasSelfLoop = true;
				}
				if(!hasSelfLoop) hasAcc = false;
			}
							
			if(hasAcc) {
				mIsEmpty = false;
				if(mSCC == null || mSCC.size() > sccList.size()) {
					mSCC = sccList;
				}
				if(Options.verbose) {
					System.out.println("Loop: " + mSCC);
				}
			}
		}
	}

}
