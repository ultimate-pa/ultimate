package de.uni_freiburg.informatik.ultimate.btor.expression;

public class ReadExpression extends BinaryExpression {

	public ReadExpression(final BtorExpression array, final BtorExpression index) {
		super(array.sort.valueSort, array, index);
	}

	@Override
	public String name() {
		return "read";
	}

}
