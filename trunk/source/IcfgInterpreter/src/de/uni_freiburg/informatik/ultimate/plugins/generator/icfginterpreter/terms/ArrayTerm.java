package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datatypes.SMTArray;

public abstract class ArrayTerm extends ExecutionTerm {
	public final ReturnType keyType;
	public final ReturnType valueType;

	public ArrayTerm(final ReturnType mKeyType, final ReturnType mValueType, final String symbol) {
		super(ReturnType.Array, symbol);
		keyType = mKeyType;
		valueType = mValueType;
	}

	@Override
	public abstract ArrayTerm simplify();

	@Override
	public abstract SMTArray evaluate(ProgramState currentState, ProgramState nextState);

	@Override
	protected abstract ArrayTerm replaceSubterms(ExecutionTerm old, ExecutionTerm replacement);

	@Override
	public ArrayTerm replaceTerm(final ExecutionTerm old, final ExecutionTerm replacement) {
		return (ArrayTerm) super.replaceTerm(old, replacement);
	}
}