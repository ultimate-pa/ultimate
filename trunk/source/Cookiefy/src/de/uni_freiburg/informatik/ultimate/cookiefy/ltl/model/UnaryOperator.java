package de.uni_freiburg.informatik.ultimate.cookiefy.ltl.model;

public abstract class UnaryOperator extends Formula {

	protected UnOp mOperator;
	protected Formula mOperand;

	public UnaryOperator(UnOp operator, Formula operand) {
		mOperator = operator;
		mOperand = operand;
	}

	public UnOp getOperator() {
		return mOperator;
	}

	public Formula getFirstOperand() {
		return mOperand;
	}

	@Override
	public String toString() {
		return "(" + mOperator + " " + mOperand + ")";
	}
}
