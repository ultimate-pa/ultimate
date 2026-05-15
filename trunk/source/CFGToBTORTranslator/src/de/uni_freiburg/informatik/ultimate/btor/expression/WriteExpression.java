package de.uni_freiburg.informatik.ultimate.btor.expression;

public class WriteExpression extends TernaryExpression {

	public WriteExpression(final BtorExpression array, final BtorExpression index, final BtorExpression arrayValue) {
		super(array.sort, array, index, arrayValue);
	}

	@Override
	public String name() {
		return "write";
	}

}
