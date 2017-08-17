package operation.intersection;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import automata.Acc;
import automata.BuchiGeneral;
import automata.IBuchi;

import gnu.trove.map.TObjectIntMap;
import gnu.trove.map.hash.TObjectIntHashMap;
import util.IntIterator;
import util.IntSet;
import util.UtilIntSet;

public class BuchiIntersection extends BuchiGeneral implements IBuchiIntersection {

	private final IBuchi mFstOperand;
	private final IBuchi mSndOperand;
	
	private final TObjectIntMap<StateIntersection> mState2Int = new TObjectIntHashMap<>();
		
	public BuchiIntersection(IBuchi fstOp, IBuchi sndOp) {
		super(fstOp.getAlphabetSize());
		this.mFstOperand = fstOp;
		this.mSndOperand = sndOp;
		computeInitialStates();
	}
	
	@Override
	public IBuchi getFstBuchi() {
		return mFstOperand;
	}

	@Override
	public IBuchi getSndBuchi() {
		return mSndOperand;
	}

	@Override
	public IBuchi getIntersection() {
		return this;
	}
	
	// take care of the acceptance
	protected StateIntersection addState(int left, int right) {
		StateIntersection state = new StateIntersection(0, this);
		state.setPairs(left, right);		
		if(mState2Int.containsKey(state)) {
			return (StateIntersection) getState(mState2Int.get(state));
		}else {
			StateIntersection newState = new StateIntersection(getStateSize(), this);
			newState.setPairs(left, right);
			int id = this.addState(newState);
			mState2Int.put(newState, id);
			getAcceptance().setAcc(newState);
			return newState;
		}
	}

	private void computeInitialStates() {
		// first compute initial states
		IntSet fstInits = mFstOperand.getInitialStates();
		IntSet sndInits = mSndOperand.getInitialStates();
		
		IntIterator fstIter = fstInits.iterator();
		while(fstIter.hasNext()) {
			int fst = fstIter.next();
			IntIterator sndIter = sndInits.iterator();
			while(sndIter.hasNext()) {
				int snd = sndIter.next();
				StateIntersection state = addState(fst, snd);				
				this.setInitial(state);
				getAcceptance().setAcc(state);
			}
		}
	}
	
	@Override
	public AccBuchiIntersection getAcceptance() {
		if(acc == null) {
			acc = new AccBuchiIntersection();
		}
		return (AccBuchiIntersection)acc;
	}
	
	private class AccBuchiIntersection implements Acc {

		private final List<IntSet> accs;
		public AccBuchiIntersection() {
			accs = new ArrayList<>();
			for(int i = 0; i < mFstOperand.getAcceptance().getAccs().size(); i ++) {
				accs.add(UtilIntSet.newIntSet());
			}
			
			for(int i = 0; i < mSndOperand.getAcceptance().getAccs().size(); i ++) {
				accs.add(UtilIntSet.newIntSet());
			}
		}
		
		protected void setAcc(StateIntersection state) {
			int i = 0;
			for(IntSet set : mFstOperand.getAcceptance().getAccs()) {
				if(set.get(state.getLeft())) {
					accs.get(i).set(state.getId());
				}
				i ++;
			}
			
			for(IntSet set : mSndOperand.getAcceptance().getAccs()) {
				if(set.get(state.getRight())) {
					accs.get(i).set(state.getId());
				}
				i ++;
			}
		}
		
		@Override
		public boolean isAccepted(IntSet set) {
			for(IntSet acc : accs) {
				if(!acc.overlap(set)) return false;
			}
			return true;
		}

		@Override
		public List<IntSet> getAccs() {
			return Collections.unmodifiableList(accs);
		}
	}

}
