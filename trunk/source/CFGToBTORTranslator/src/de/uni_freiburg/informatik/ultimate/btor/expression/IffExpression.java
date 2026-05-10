package de.uni_freiburg.informatik.ultimate.btor.expression;

public class IffExpression extends BinaryExpression {

	public IffExpression(final BtorExpression left, final BtorExpression right) {
		super(left.sort, left, right);
	}

	@Override
	public String name() {
		return "iff";
	}

}
