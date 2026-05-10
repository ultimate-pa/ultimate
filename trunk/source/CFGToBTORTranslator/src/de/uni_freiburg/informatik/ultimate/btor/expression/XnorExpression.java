package de.uni_freiburg.informatik.ultimate.btor.expression;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

public class XnorExpression extends BinaryExpression {

	public XnorExpression(final BtorExpression left, final BtorExpression right) {
		super(new BtorSort(left.sort.size), left, right);
	}

	@Override
	public String name() {
		return "xnor";
	}

}
