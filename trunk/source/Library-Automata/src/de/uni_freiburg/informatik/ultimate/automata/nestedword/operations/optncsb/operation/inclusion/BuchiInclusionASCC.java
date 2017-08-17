package operation.inclusion;

import java.util.BitSet;
import java.util.HashMap;

import java.util.List;
import java.util.Map;
import java.util.Stack;

import automata.BuchiGeneral;
import automata.IState;
import automata.IBuchi;
import complement.StateNCSB;
import main.TaskInclusion;
import util.IPair;
import util.IntIterator;
import util.IntSet;
import util.IntStack;
import util.PairXY;
import util.Timer;

/**
 * ASCC algorithm from the paper Comparison of Algorithms for Checking Emptiness on Buchi Automata
 *                by Andreas Gaiser and Stefan Schwoon
 * **/
public class BuchiInclusionASCC extends BuchiInclusion {
		
	public BuchiInclusionASCC(TaskInclusion task, IBuchi fstOp, IBuchi sndOp) {
		super(task, fstOp, sndOp);
	}
		
	/**
	 * try to compute the product of mFstOperand and mSndComplement
	 * by constructing the complement of mSndOperand
	 * */
	
	public Boolean isIncluded() {
		ASCC scc = new ASCC();
//		System.out.println(mResult.toString());
//		System.out.println(mFstFinalStates + ", " + mSndFinalStates);
//		System.out.println("acc:" + scc.getAcceptedSCC());
//		System.out.println(scc.getPrefix() + ", (" + scc.getLoop() + ")");
		return scc.mIsEmpty;
	}

	@Override
	public IPair<List<Integer>, List<Integer>> getCounterexampleWord() {
		return null;
	}

	@Override
	public IPair<List<IState>, List<IState>> getCounterexampleRun() {
		return null;
	}
	
	// ---------------------------- part for SCC decomposition -------------
	/**
	 * SCC Decomposition
	 * */
	private class ASCC {
		
		private int mIndex=0;
		private final Stack<PairXY<Integer, BitSet>> mRootsStack ;
		private final Map<Integer, Integer> mDfsNum;
		private final IntStack mActiveStack ;
		private final BitSet mCurrent;
		
		private Boolean mIsEmpty = true;
		
		private final Timer mTimer;
		
		public ASCC() {
			
			this.mRootsStack = new Stack<>();
			this.mActiveStack = new IntStack();
			this.mDfsNum = new HashMap<>();
			this.mCurrent = new BitSet();
			this.mTimer = new Timer();
			
			mTimer.start();
			IntIterator iter = mResult.getInitialStates().iterator();
			while(iter.hasNext()) {
				int n = iter.next();

				if(! mDfsNum.containsKey(n)){
					dfs(n);
					if(mIsEmpty == null ||  ! mIsEmpty.booleanValue())
						break ;
				}
			}
		}
		
		private boolean terminate() {
			if(mTimer.tick() > mTask.getTimeBound()) 
				return true;
			return false;
		}
		
		
		// make use of tarjan algorithm
		void dfs(int s) {
			
			if(terminate()) {
				mIsEmpty = null;
				return ;
			}
			
			mIndex++;
			mDfsNum.put(s, mIndex);
			mActiveStack.push(s);
			mCurrent.set(s);
			
			InclusionPairNCSB pair = mPairNCSBArray.get(s); //v must in mPairArray
			// get flags
			BitSet flags = new BitSet();
			if(mFstOperand.isFinal(pair.getFstElement())) {
				flags.set(0);
			}
			
			if(pair.getSndElement().getBSet().isEmpty()) {
				flags.set(1);
			}
			
			mRootsStack.push(new PairXY<>(s, flags));
			
			//TODO only get enabled letters
			for(int letter = 0; letter < mFstOperand.getAlphabetSize(); letter ++) {
				// X states from first BA 
				IntSet fstSuccs = mFstOperand.getState(pair.getFstElement()).getSuccessors(letter);
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
						if(! mDfsNum.containsKey(stateSucc.getId())){
							dfs(stateSucc.getId());
							if(mIsEmpty == null ||  ! mIsEmpty.booleanValue())
								return ;
						}else if(mCurrent.get(stateSucc.getId())){
							BitSet B = new BitSet();
							int u;
							do {
								PairXY<Integer, BitSet> p = mRootsStack.pop();
								B.or(p.getSndElement());
								if(B.cardinality() == 2) {
									mIsEmpty = false;
									return ;
								}
								u = p.getFstElement();
							}while(mDfsNum.get(u) > mDfsNum.get(stateSucc.getId()));
							mRootsStack.push(new PairXY<>(u, B));
						}
					}
				}
			}

			if(mRootsStack.peek().getFstElement().intValue() == s){
				
				mRootsStack.pop();
				int u;
				do {
					u = mActiveStack.pop();
					mCurrent.clear(u);
				}while(u != s);	
			}
		}
		
	}
	

	@Override
	public String getName() {
		// TODO Auto-generated method stub
		return "ASCC";
	}




}
