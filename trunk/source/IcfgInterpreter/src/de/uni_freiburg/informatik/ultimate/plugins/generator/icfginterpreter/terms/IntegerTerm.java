package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;

public abstract class IntegerTerm extends ExecutionTerm {
	public IntegerTerm(final String symbol) {
		super(ReturnType.Int, symbol);
	}

	public abstract IntegerTerm negate();

	@Override
	public abstract IntegerTerm simplify();

	@Override
	public abstract Long evaluate(ProgramState currentState, ProgramState nextState);

	@Override
	protected abstract IntegerTerm replaceSubterms(ExecutionTerm old, ExecutionTerm replacement);

	@Override
	public IntegerTerm replaceTerm(final ExecutionTerm old, final ExecutionTerm replacement) {
		return (IntegerTerm) super.replaceTerm(old, replacement);
	}
}