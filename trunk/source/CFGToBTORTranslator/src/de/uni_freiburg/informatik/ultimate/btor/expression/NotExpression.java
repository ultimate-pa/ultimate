package de.uni_freiburg.informatik.ultimate.btor.expression;

public class NotExpression extends UnaryExpression {

	public NotExpression(final BtorExpression child) {
		super(child.sort, child);
	}

	@Override
	public String name() {
		return "not";
	}
}
