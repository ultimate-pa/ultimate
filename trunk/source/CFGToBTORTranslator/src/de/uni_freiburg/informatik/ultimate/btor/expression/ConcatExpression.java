package de.uni_freiburg.informatik.ultimate.btor.expression;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

public class ConcatExpression extends BinaryExpression {

	public ConcatExpression(final BtorExpression first, final BtorExpression second) {
		super(new BtorSort(first.sort.size + second.sort.size), first, second);
	}

	@Override
	public String name() {
		return "concat";
	}

}
