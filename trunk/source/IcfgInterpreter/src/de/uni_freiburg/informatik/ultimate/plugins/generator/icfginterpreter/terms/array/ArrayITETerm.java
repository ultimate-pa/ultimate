package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datatypes.SMTArray;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.ITETerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class ArrayITETerm extends ArrayTerm {
	private final ITETerm<ArrayTerm> mITE;

	public ArrayITETerm(final BooleanTerm condition, final ArrayTerm ifTerm, final ArrayTerm elseTerm) {
		super(ifTerm.keyType, ifTerm.valueType, ITETerm.mSymbol);
		assert ifTerm.keyType == elseTerm.keyType && ifTerm.valueType == elseTerm.valueType;
		mITE = new ITETerm<>(condition, ifTerm, elseTerm);
	}

	private ArrayITETerm(final ITETerm<ArrayTerm> ite) {
		super(ite.mB.keyType, ite.mB.valueType, ITETerm.mSymbol);
		mITE = ite;
	}

	@Override
	public ArrayITETerm simplify() {
		return new ArrayITETerm(mITE.mCondition.simplify(), mITE.mB.simplify(), mITE.mC.simplify());
	}

	@Override
	public ArrayList<ExecutionTerm> getSubTerms() {
		return mITE.getSubTerms();
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		return mITE.toString(out, depth);
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof ArrayITETerm)) {
			return false;
		}
		return mITE.equals(((ArrayITETerm) b).mITE);
	}

	@Override
	public int hashCode() {
		return mITE.hashCode();
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		return mITE.getVariables();
	}

	@Override
	public Term toSMTTerm(final Theory theory) {
		return mITE.toSMTTerm(theory);
	}

	@Override
	public SMTArray evaluate(final ProgramState currentState, final ProgramState nextState) {
		return (SMTArray) mITE.evaluate(currentState, nextState);
	}

	@Override
	public String toCode() {
		return mITE.toCode();
	}

	@Override
	protected ArrayITETerm replaceSubterms(final ExecutionTerm old, final ExecutionTerm replacement) {
		final BooleanTerm mA = mITE.mCondition.replaceTerm(old, replacement);
		final ArrayTerm mB = mITE.mB.replaceTerm(old, replacement);
		final ArrayTerm mC = mITE.mC.replaceTerm(old, replacement);

		return new ArrayITETerm(new ITETerm<>(mA, mB, mC));
	}
}