package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.SMTArray;

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

	// @Override
	// public abstract ArrayDomain<keyType, valueType> evaluate(HashMap<Variable, Domain<?>> variableDomains);

	@Override
	public abstract SMTArray evaluate(ProgramState state);
}