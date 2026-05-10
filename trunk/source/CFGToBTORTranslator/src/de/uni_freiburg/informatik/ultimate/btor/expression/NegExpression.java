package de.uni_freiburg.informatik.ultimate.btor.expression;

public class NegExpression extends UnaryExpression {

	public NegExpression(final BtorExpression child) {
		super(child.sort, child);
	}

	@Override
	public String name() {
		return "neg";
	}
}
