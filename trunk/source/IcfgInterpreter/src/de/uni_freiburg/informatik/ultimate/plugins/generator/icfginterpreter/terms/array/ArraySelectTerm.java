package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datatypes.SMTArray;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ReturnType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.SelectTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class ArraySelectTerm extends ArrayTerm {
	private final SelectTerm mSelect;

	public ArraySelectTerm(final ArrayTerm mArray, final ExecutionTerm mIndex) {
		super(mArray.keyType, mArray.valueType, SelectTerm.mSymbol);
		assert mArray.valueType == ReturnType.Array;
		mSelect = new SelectTerm(mArray, mIndex);
	}

	private ArraySelectTerm(final SelectTerm select) {
		super(select.getArray().keyType, select.getArray().valueType, SelectTerm.mSymbol);
		assert select.getArray().valueType == ReturnType.Array;
		mSelect = select;
	}

	@Override
	public ArraySelectTerm simplify() {
		final ArrayTerm mArray = mSelect.getArray().simplify();
		final ExecutionTerm mIndex = mSelect.getIndex().simplify();

		return new ArraySelectTerm(mArray, mIndex);
	}

	@Override
	public ArrayList<ExecutionTerm> getSubTerms() {
		return mSelect.getSubTerms();
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		return mSelect.toString(out, depth);
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof ArraySelectTerm)) {
			return false;
		}
		return mSelect.equals(((ArraySelectTerm) b).mSelect);
	}

	@Override
	public int hashCode() {
		return mSelect.hashCode();
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		return mSelect.getVariables();
	}

	@Override
	public Term toSMTTerm(final Theory theory) {
		return mSelect.toSMTTerm(theory);
	}

	@Override
	public SMTArray evaluate(final ProgramState currentState, final ProgramState nextState) {
		return (SMTArray) mSelect.evaluate(currentState, nextState);
	}

	@Override
	public String toCode() {
		return "((SMTArray) " + mSelect.toCode() + ")";
	}

	@Override
	protected ArraySelectTerm replaceSubterms(final ExecutionTerm old, final ExecutionTerm replacement) {
		return new ArraySelectTerm(mSelect.replaceTerm(old, replacement));
	}
}
