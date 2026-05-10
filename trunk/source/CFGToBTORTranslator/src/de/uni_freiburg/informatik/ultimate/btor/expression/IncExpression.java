package de.uni_freiburg.informatik.ultimate.btor.expression;

public class IncExpression extends UnaryExpression {

	public IncExpression(final BtorExpression child) {
		super(child.sort, child);
	}

	@Override
	public String name() {
		return "incNotExpression.java";
	}
}
