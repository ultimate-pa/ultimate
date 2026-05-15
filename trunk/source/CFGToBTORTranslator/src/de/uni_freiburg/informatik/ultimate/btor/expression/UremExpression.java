package de.uni_freiburg.informatik.ultimate.btor.expression;

public class UremExpression extends BinaryExpression {

	public UremExpression(final BtorExpression left, final BtorExpression right) {
		super(left.sort, left, right);
	}

	@Override
	public String name() {
		return "urem";
	}

}
