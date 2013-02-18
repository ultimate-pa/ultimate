package de.uni_freiburg.informatik.ultimate.cookiefy.ltl.model;

public class Finally extends UnaryOperator {

	public Finally(Formula operand) {
		super(UnOp.FINALLY, operand);
	}
	
	@Override
	public String toString() {
		return super.toString();
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
