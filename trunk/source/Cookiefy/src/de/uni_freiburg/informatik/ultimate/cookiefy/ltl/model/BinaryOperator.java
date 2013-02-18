package de.uni_freiburg.informatik.ultimate.cookiefy.ltl.model;

public abstract class BinaryOperator extends Formula {

	protected BinOp mOperator;
	protected Formula mFirstOperand;
	protected Formula mLastOperand;

	public BinaryOperator(BinOp operator, Formula first, Formula last) {
		mOperator = operator;
		mFirstOperand = first;
		mLastOperand = last;
	}

	public BinOp getOperator() {
		return mOperator;
	}

	public Formula getFirstOperand() {
		return mFirstOperand;
	}

	public Formula getLastOperand() {
		return mLastOperand;
	}

	@Override
	public String toString() {
		return "(" + mFirstOperand + " " + mOperator + " " + mLastOperand + ")";
	}
}
