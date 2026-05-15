package de.uni_freiburg.informatik.ultimate.btor.expression;

public class SrlExpression extends BinaryExpression {

	public SrlExpression(final BtorExpression left, final BtorExpression right) {
		super(left.sort, left, right);
	}

	@Override
	public String name() {
		return "srl";
	}

}
