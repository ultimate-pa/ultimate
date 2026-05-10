package de.uni_freiburg.informatik.ultimate.btor.expression;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

public class EqExpression extends BinaryExpression {

	public EqExpression(final BtorExpression left, final BtorExpression right) {
		super(new BtorSort(1), left, right);
	}

	@Override
	public String name() {
		return "eq";
	}

}
