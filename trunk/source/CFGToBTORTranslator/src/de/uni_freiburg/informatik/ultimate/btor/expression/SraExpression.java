package de.uni_freiburg.informatik.ultimate.btor.expression;

public class SraExpression extends BinaryExpression {

	public SraExpression(final BtorExpression left, final BtorExpression right) {
		super(left.sort, left, right);
	}

	@Override
	public String name() {
		return "sra";
	}

}
