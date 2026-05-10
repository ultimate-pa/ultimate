package de.uni_freiburg.informatik.ultimate.btor.expression;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

public class ReadExpression extends BinaryExpression {

	public ReadExpression(final BtorExpression array, final BtorExpression index) {
		super(new BtorSort(index.sort.size), array, index);
	}

	@Override
	public String name() {
		return "read";
	}

}
