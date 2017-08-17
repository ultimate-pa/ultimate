package operation.universality;

import java.util.BitSet;
import java.util.List;

import automata.IBuchi;
import automata.IState;
import complement.StateNCSB;
import util.IPair;
import util.IntIterator;
import util.IntSet;
import util.IntStack;
import util.Timer;

// only plain nested DFS
public class BuchiUniversalityNestedDFSAntichain extends BuchiUniversality {

	public BuchiUniversalityNestedDFSAntichain(IBuchi buchi) {
		super(buchi);
		// TODO Auto-generated constructor stub
	}

	@Override
	public Boolean isUniversal() {
		// TODO Auto-generated method stub
		NestedDFS dfs = new NestedDFS(10 * 1000);
		return dfs.mIsEmpty;
	}

	@Override
	public IPair<List<Integer>, List<Integer>> getCounterexampleWord() {
		// TODO Auto-generated method stub
		return null;
	}
	
	// search for accepting SCC in the complement
	
	private class NestedDFS {
		private final IntStack mFstStack;
		private final IntStack mSndStack;
		private final BitSet mFstTable;
		private final BitSet mSndTable;
		private Boolean mIsEmpty = true;
		private final long TIME_LIMIT;
		private Timer mTimer;
		
		NestedDFS(int timeLimit) {
			this.TIME_LIMIT = timeLimit;
			this.mFstStack = new IntStack();
			this.mSndStack = new IntStack();
			this.mFstTable = new BitSet();
			this.mSndTable = new BitSet();
			this.mTimer = new Timer();
			mTimer.start();
			explore();
		}

		private void explore() {
			// TODO Auto-generated method stub
			IntIterator iter = mBuchiComplement.getInitialStates().iterator();
			while(iter.hasNext()) {
				int n = iter.next();
				if(!mFstTable.get(n) && !terminate()){
					fstDFS(n);
				}
			}
		}
		
		private boolean terminate() {
			if(mTimer.tick() > TIME_LIMIT) 
				return true;
			return false;
		}

		private void fstDFS(int n) {
			
			if(terminate()) {
				mIsEmpty = null;
				return ;
			}
			// TODO Auto-generated method stub
			mFstStack.push(n);
			mFstTable.set(n);
			
			IState state = mBuchiComplement.getState(n);
			//TODO only get enabled letters
			for(int letter = 0; letter < mBuchiComplement.getAlphabetSize(); letter ++) {
				IntSet succs = state.getSuccessors(letter);
				IntIterator iter = succs.iterator();
				while(iter.hasNext()) {
					int succ = iter.next();
					if(! mFstTable.get(succ)) {
						fstDFS(succ);
						if(mIsEmpty == null || mIsEmpty.booleanValue() == false) return;
					}
				}
			}
			
			if(mBuchiComplement.isFinal(n)) {
				sndDFS(n);
			}
			
			mFstStack.pop();
		}
				
		
		private void sndDFS(int n) {
			
			if(terminate()) {
				mIsEmpty = null;
				return ;
			}
			
			mSndStack.push(n);
			mSndTable.set(n);

			IState state = mBuchiComplement.getState(n);
			//TODO only get enabled letters
			for(int letter = 0; letter < mBuchiComplement.getAlphabetSize(); letter ++) {
				IntSet succs = state.getSuccessors(letter);
				IntIterator iter = succs.iterator();
				while(iter.hasNext()) {
					int succ = iter.next();
					// the only difference lies here
					if(mFstStack.contains(succ)
					|| hasCoveredStatesInStack(succ)) {
						mIsEmpty = false;
						return ;
					}else if(! mSndTable.get(succ)) {
						sndDFS(succ);
						if(mIsEmpty == null || mIsEmpty.booleanValue() == false) return;
					}
				}
			}
			
			mSndStack.pop();

		}
		
		// we know that the stack cannot have two same elements
		private boolean hasCoveredStatesInStack(int t) {
			StateNCSB stateT = (StateNCSB) mBuchiComplement.getState(t);
			IntSet items = mFstStack.getItems();
			items.clear(mFstStack.peek());
			// only keep final states in stack
			items.and(mBuchiComplement.getFinalStates()); 
			IntIterator iter = items.iterator();
			while(iter.hasNext()) {
			    int u = iter.next();
				StateNCSB stateU = (StateNCSB) mBuchiComplement.getState(u);
				if(stateU.coveredBy(stateT)) return true;
			}
			return false;
		}
	}
		

}
