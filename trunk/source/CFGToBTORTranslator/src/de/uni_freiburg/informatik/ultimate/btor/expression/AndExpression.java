package de.uni_freiburg.informatik.ultimate.btor.expression;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

public class AndExpression extends BinaryExpression {

	public AndExpression(final BtorExpression left, final BtorExpression right) {
		super(new BtorSort(left.sort.size), left, right);
	}

	@Override
	public String name() {
		return "and";
	}

}
