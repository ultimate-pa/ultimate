package de.uni_freiburg.informatik.ultimate.btor.expression;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

public class WriteExpression extends TernaryExpression {

	public WriteExpression(final BtorExpression array, final BtorExpression index, final BtorExpression arrayValue) {
		super(new BtorSort(1), array, index, arrayValue);
	}

	@Override
	public String name() {
		return "write";
	}

}
