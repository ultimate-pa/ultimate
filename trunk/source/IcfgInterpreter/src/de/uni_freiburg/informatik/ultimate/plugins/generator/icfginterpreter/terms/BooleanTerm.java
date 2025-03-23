package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;

public abstract class BooleanTerm extends ExecutionTerm {
	public BooleanTerm(final String symbol) {
		super(ReturnType.Boolean, symbol);
	}

	public abstract BooleanTerm negate();

	@Override
	public abstract BooleanTerm simplify();

	@Override
	public abstract Boolean evaluate(ProgramState currentState, ProgramState nextState);
}