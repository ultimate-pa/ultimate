package de.uni_freiburg.informatik.ultimate.btor.expression;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

public class ITEExpression extends TernaryExpression {

	public ITEExpression(final BtorExpression ifEx, final BtorExpression thenEx, final BtorExpression elseEx) {
		super(new BtorSort(1), ifEx, thenEx, elseEx);
	}

	@Override
	public String name() {
		return "ite";
	}

}