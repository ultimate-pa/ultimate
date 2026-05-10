package de.uni_freiburg.informatik.ultimate.btor.expression;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

public class RedandExpression extends UnaryExpression {

	public RedandExpression(final BtorExpression child) {
		super(new BtorSort(1), child);
	}

	@Override
	public String name() {
		return "redand";
	}
}
