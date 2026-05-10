package de.uni_freiburg.informatik.ultimate.btor.expression;

public class DecExpression extends UnaryExpression {

	public DecExpression(final BtorExpression child) {
		super(child.sort, child);
	}

	@Override
	public String name() {
		return "dec";
	}
}
