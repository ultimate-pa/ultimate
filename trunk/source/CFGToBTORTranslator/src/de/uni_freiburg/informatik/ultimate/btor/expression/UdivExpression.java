package de.uni_freiburg.informatik.ultimate.btor.expression;

public class UdivExpression extends BinaryExpression {

	public UdivExpression(final BtorExpression left, final BtorExpression right) {
		super(left.sort, left, right);
	}

	@Override
	public String name() {
		return "udiv";
	}

}
