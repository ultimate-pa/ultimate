package de.uni_freiburg.informatik.ultimate.btor.expression;

public class ITEExpression extends TernaryExpression {

	public ITEExpression(final BtorExpression ifEx, final BtorExpression thenEx, final BtorExpression elseEx) {
		super(thenEx.sort, ifEx, thenEx, elseEx);
	}

	@Override
	public String name() {
		return "ite";
	}

}