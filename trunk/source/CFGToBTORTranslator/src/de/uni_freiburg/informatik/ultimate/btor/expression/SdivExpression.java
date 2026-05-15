package de.uni_freiburg.informatik.ultimate.btor.expression;

public class SdivExpression extends BinaryExpression {

	public SdivExpression(final BtorExpression left, final BtorExpression right) {
		super(left.sort, left, right);
	}

	@Override
	public String name() {
		return "sdiv";
	}

}
