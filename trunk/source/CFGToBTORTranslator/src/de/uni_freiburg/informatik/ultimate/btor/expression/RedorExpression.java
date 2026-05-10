package de.uni_freiburg.informatik.ultimate.btor.expression;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

public class RedorExpression extends UnaryExpression {

	public RedorExpression(final BtorExpression child) {
		super(new BtorSort(1), child);
	}

	@Override
	public String name() {
		return "redor";
	}
}
