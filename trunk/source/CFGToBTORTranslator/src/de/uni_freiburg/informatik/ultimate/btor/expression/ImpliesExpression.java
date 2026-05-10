package de.uni_freiburg.informatik.ultimate.btor.expression;

public class ImpliesExpression extends BinaryExpression {

	public ImpliesExpression(final BtorExpression left, final BtorExpression right) {
		super(left.sort, left, right);
	}

	@Override
	public String name() {
		return "implies";
	}

}
