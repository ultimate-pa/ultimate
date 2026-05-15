package de.uni_freiburg.informatik.ultimate.btor.expression;

public class SmodExpression extends BinaryExpression {

	public SmodExpression(final BtorExpression left, final BtorExpression right) {
		super(left.sort, left, right);
	}

	@Override
	public String name() {
		return "smod";
	}

}
