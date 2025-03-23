package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.BitVector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;

public abstract class BitVectorTerm extends ExecutionTerm {
	protected final int mLength;

	public BitVectorTerm(final String symbol, final int length) {
		super(ReturnType.BitVector, symbol);
		assert length > 0;
		mLength = length;
	}

	@Override
	public abstract BitVectorTerm simplify();

	@Override
	public abstract BitVector evaluate(final ProgramState currentState, final ProgramState nextState);
}
