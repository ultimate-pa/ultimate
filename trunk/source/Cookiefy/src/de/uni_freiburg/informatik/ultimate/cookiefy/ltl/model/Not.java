package de.uni_freiburg.informatik.ultimate.cookiefy.ltl.model;

public class Not extends UnaryOperator {

	public Not(Formula operand) {
		super(UnOp.NOT, operand);
	}
	
	@Override
	public String toString() {
		return mOperator + " " + mOperand ;
	}
	
	@Override
	public void acceptPreOrder(Visitor visitor) {
		visitor.visit(this);
		mOperand.acceptPreOrder(visitor);
	}
	
	@Override
	public void acceptInOrder(Visitor visitor) {
		mOperand.acceptInOrder(visitor);
		visitor.visit(this);
	}

	@Override
	public void acceptPostOrder(Visitor visitor) {
		mOperand.acceptInOrder(visitor);
		visitor.visit(this);
	}
}
