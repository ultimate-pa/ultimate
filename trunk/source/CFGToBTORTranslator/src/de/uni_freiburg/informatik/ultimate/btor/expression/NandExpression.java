package de.uni_freiburg.informatik.ultimate.btor.expression;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

public class NandExpression extends BinaryExpression {

	public NandExpression(final BtorExpression left, final BtorExpression right) {
		super(new BtorSort(left.sort.size), left, right);
	}

	@Override
	public String name() {
		return "nand";
	}

}
