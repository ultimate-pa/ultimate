package de.uni_freiburg.informatik.ultimate.modelcheckerutils.errortrace;

import de.uni_freiburg.informatik.ultimate.logic.Term;

public class ErrorInvariant {
	private int mStartIndex = 0;
	private int mEndIndex = 0;
	private int mIndex = 0;
	private Term mInvariant = null;
	
	public ErrorInvariant(Term inv, int index, Term[] formulas) {
		setStartOfIntervall(index);
		setEndOfIntervall(index);
		mIndex = index;
		mInvariant = inv;
	}
	
	public int getStartOfIntervall() {
		return mStartIndex;
	}
	
	public void setStartOfIntervall(int startOfIntervall) {
		mStartIndex = startOfIntervall;
	}
	
	public int getEndOfIntervall() {
		return mEndIndex;
	}
	
	public void setEndOfIntervall(int endOfIntervall) {
		mEndIndex = endOfIntervall;
	}
	
	public int getIndex() {
		return mIndex;
	}
	
	public int getLength() {
		return this.getEndOfIntervall() - this.getStartOfIntervall();
	}
	
	public Term getInvariant() {
		return mInvariant;
	}
}
