package operation.inclusion;

import java.util.BitSet;
import java.util.List;
import java.util.Stack;

import automata.BuchiGeneral;
import automata.IBuchi;
import automata.IState;
import complement.StateNCSB;
import main.TaskInclusion;
import util.IPair;
import util.IntIterator;
import util.IntSet;

public class BuchiInclusionNestedDFS extends BuchiInclusion {
	

	public BuchiInclusionNestedDFS(TaskInclusion task, IBuchi fstOp, IBuchi sndOp) {
		super(task, fstOp, sndOp);
	}
	
	@Override
	public IPair<List<Integer>, List<Integer>> getCounterexampleWord() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IPair<List<IState>, List<IState>> getCounterexampleRun() {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * try to compute the product of mFstOperand and mSndComplement
	 * and avoid exploring unnecessary states as much as possible
	 * */
	
	public Boolean isIncluded() {
		NestedDFS finder = new NestedDFS();
//		System.out.println(mFstOperand.toDot());
//		System.out.println(mSndOperand.toDot());
////		System.out.println(mSndComplement.toDot());
//		System.out.println(mResult.toDot());
//		System.out.println(mFstFinalStates + "," + mSndFinalStates);
		return finder.mIsEmpty;
	}
	
	// ---------------------------- part for SCC decomposition -------------
	
	private class NestedDFS {
		private final Stack<Integer> mFstStack;
		private final Stack<Integer> mSndStack;
		private final BitSet mFstTable;
		private final BitSet mSndTable;
		private Boolean mIsEmpty = true;
		private final BitSet mOnlyInFstStack;
		
		NestedDFS() {

			this.mFstStack = new Stack<>();
			this.mSndStack = new Stack<>();
			this.mFstTable = new BitSet();
			this.mSndTable = new BitSet();
			this.mOnlyInFstStack = new BitSet();
			explore();
		}

		private void explore() {
			// TODO Auto-generated method stub
			IntIterator iter = mResult.getInitialStates().iterator();
			while(iter.hasNext()) {
				int n = iter.next();
				if(!mFstTable.get(n) && !terminate()){
					fstDFS(n);
				}
			}
		}
		
		private boolean terminate() {
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
			mOnlyInFstStack.set(n);
			// explore until we see a final state
			
			InclusionPairNCSB pair = mPairNCSBArray.get(n); //n must in mPairArray
			
			//TODO only get enabled letters
			for(int letter = 0; letter < mFstOperand.getAlphabetSize(); letter ++) {
				// X states from first BA 
				IntSet fstSuccs = mFstOperand.getSuccessors(pair.getFstElement(), letter);
				if(fstSuccs.isEmpty()) continue;
				// Y states from second BA
				IntSet sndSuccs = pair.getSndElement().getSuccessors(letter);
				IntIterator fstIter = fstSuccs.iterator();
				while(fstIter.hasNext()) {
					int fstSucc = fstIter.next();
					IntIterator sndIter = sndSuccs.iterator();
					while(sndIter.hasNext()) {
						int sndSucc = sndIter.next();
						// pair (X, Y)
						StateNCSB yState = (StateNCSB) mSndComplement.getState(sndSucc);
						InclusionPairNCSB pairSucc = new InclusionPairNCSB(fstSucc, yState);
						IState stateSucc = getOrAddState(pairSucc);
						mPairStateMap.get(pair).addSuccessor(letter, stateSucc.getId());
						// now current successor is stateSucc
						if(! mFstTable.get(stateSucc.getId())) fstDFS(stateSucc.getId());
					}
				}
			}
			
			// go to find a loop if n is final
			if(mSndComplement.isFinal(pair.getSndElement().getId())) {
				sndDFS(n);
				if(! mIsEmpty ) return ;
			}
			
			
			mFstStack.pop();
			mOnlyInFstStack.clear(n);
		}
				
		private final BitSet mFstFinalInSndStack = new BitSet();
		
		private void sndDFS(int n) {
			
			if(terminate()) {
				mIsEmpty = null;
				return ;
			}
			
			mSndStack.push(n);
			mSndTable.set(n);
			InclusionPairNCSB pair = mPairNCSBArray.get(n); //n must in mPairArray
			// fst has final in the loop
			if(mFstOperand.isFinal(pair.getFstElement())) {
				mFstFinalInSndStack.set(n);
			}
			
			for(int letter = 0; letter < mFstOperand.getAlphabetSize(); letter ++) {
				// X states from first BA 
				IntSet fstSuccs = mFstOperand.getSuccessors(pair.getFstElement(), letter);
				if(fstSuccs.isEmpty()) continue;
				// Y states from second BA
				IntSet sndSuccs = pair.getSndElement().getSuccessors(letter);
				IntIterator fstIter = fstSuccs.iterator();
				while(fstIter.hasNext()) {
					int fstSucc = fstIter.next();
					IntIterator sndIter = sndSuccs.iterator();
					while(sndIter.hasNext()) {
						int sndSucc = sndIter.next();
						// pair (X, Y)
						StateNCSB yState = (StateNCSB) mSndComplement.getState(sndSucc);
						InclusionPairNCSB pairSucc = new InclusionPairNCSB(fstSucc, yState);
						IState stateSucc = getOrAddState(pairSucc);
						mPairStateMap.get(pair).addSuccessor(letter, stateSucc.getId());
						// now current successor is stateSucc
						if(existLoop(stateSucc.getId()) && ! mFstFinalInSndStack.isEmpty()) {
							mIsEmpty = false;
							return ;
						}else if(! mSndTable.get(stateSucc.getId())){
							sndDFS(stateSucc.getId());
							if(! mIsEmpty ) return ;
						}
					}
				}
			}
			
			mSndStack.pop();
			mFstFinalInSndStack.clear(n);
		}
		
		// either there exists a state t in stack 1
		// or there exists a final state u such that u is not the top element and is covered by t 
		private boolean existLoop(int t) {
			
			if(mOnlyInFstStack.get(t)) {
					return true;
			}
			
			BitSet accs = (BitSet) mFstFinalStates.clone(); // get current final states
			accs.and(mOnlyInFstStack);                    // get only final states in stack1
			
			accs.clear(mFstStack.peek());                 // remove the top element
			InclusionPairNCSB tPair = mPairNCSBArray.get(t);
			for(int u = accs.nextSetBit(0); u >= 0; u = accs.nextSetBit(u + 1)) {
				InclusionPairNCSB uPair = mPairNCSBArray.get(u);
				if(uPair.coveredBy(tPair)) return true;
			}
			return false;
		}

	}
		

	@Override
	public String getName() {
		// TODO Auto-generated method stub
		return "NestedDFS";
	}



}

