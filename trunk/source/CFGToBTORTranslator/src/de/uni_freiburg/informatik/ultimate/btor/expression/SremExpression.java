package de.uni_freiburg.informatik.ultimate.btor.expression;

public class SremExpression extends BinaryExpression {

	public SremExpression(final BtorExpression left, final BtorExpression right) {
		super(left.sort, left, right);
	}

	@Override
	public String name() {
		return "srem";
	}

}
