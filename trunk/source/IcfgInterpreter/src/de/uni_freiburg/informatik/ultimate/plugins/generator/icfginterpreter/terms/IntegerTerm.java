package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;

public abstract class IntegerTerm extends ExecutionTerm {
	public IntegerTerm(final String symbol) {
		super(ReturnType.Int, symbol);
	}

	public abstract IntegerTerm negate();

	@Override
	public abstract IntegerTerm simplify();

	// @Override
	// public abstract IntegerDomain evaluate(HashMap<Variable<?>, Domain<?>> variableDomains);

	@Override
	public abstract Integer evaluate(ProgramState currentState, ProgramState nextState);
}