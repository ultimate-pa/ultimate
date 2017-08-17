package operation.intersection;


import automata.IBuchi;
import automata.StateGeneral;
import util.IntIterator;
import util.IntSet;
import util.UtilIntSet;

public class StateIntersection extends StateGeneral {

	private final BuchiIntersection mBuchiIntersection;
	
	public StateIntersection(int id, BuchiIntersection buchi) {
		super(id);
		this.mBuchiIntersection = buchi;
	}
	
	private int mLeft;
	private int mRight;
	
	protected void setPairs(int left, int right) {
		mLeft = left;
		mRight = right;
	}
	
	public boolean equals(Object obj) {
		if(!(obj instanceof StateIntersection)) {
			return false;
		}
		StateIntersection other = (StateIntersection)obj;
		return mLeft == other.mLeft && mRight == other.mRight;
	}
	
	public String toString() {
		return "(" + mLeft + "," + mRight + ")";
	}
	
	int hashCode;
	boolean hasCode = false;
	@Override
	public int hashCode() {
		if(hasCode) return hashCode;
		else {
			hasCode = true;
			hashCode = mLeft * mBuchiIntersection.getStateSize() + mRight;
		}
		return hashCode;
	}
	
	public int getLeft() {
		return mLeft;
	}
	
	public int getRight() {
		return mRight;
	}
	
	private IntSet visitedLetters = UtilIntSet.newIntSet();
	
	@Override
	public IntSet getSuccessors(int letter) {
		if(visitedLetters.get(letter)) {
			return super.getSuccessors(letter);
		}
		
		visitedLetters.set(letter);
		// compute successors
		IBuchi fstOp = mBuchiIntersection.getFstBuchi();
		IBuchi sndOp = mBuchiIntersection.getSndBuchi();
		IntSet fstSuccs = fstOp.getState(mLeft).getSuccessors(letter);
		IntSet sndSuccs = sndOp.getState(mRight).getSuccessors(letter);
		
		IntIterator fstIter = fstSuccs.iterator();
		while(fstIter.hasNext()) {
			int fstSucc = fstIter.next();
			IntIterator sndIter = sndSuccs.iterator();
			while(sndIter.hasNext()) {
				int sndSucc = sndIter.next();
				// pair (X, Y)
                StateIntersection succ = mBuchiIntersection.addState(fstSucc, sndSucc);                
				this.addSuccessor(letter, succ.getId());
			}
	    }

		return super.getSuccessors(letter);
	}

}
