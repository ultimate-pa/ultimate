package de.uni_freiburg.informatik.ultimate.btor.expression;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

public class SgteExpression extends BinaryExpression {

	public SgteExpression(final BtorExpression left, final BtorExpression right) {
		super(new BtorSort(1), left, right);
	}

	@Override
	public String name() {
		return "sgte";
	}

}
