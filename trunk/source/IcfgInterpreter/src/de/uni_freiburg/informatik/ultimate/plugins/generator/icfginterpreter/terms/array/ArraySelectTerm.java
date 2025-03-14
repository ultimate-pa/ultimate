package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.SMTArray;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.SelectTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class ArraySelectTerm extends ArrayTerm {
	private final SelectTerm select;

	public ArraySelectTerm(final ArrayTerm mArray, final ExecutionTerm mIndex) {
		super(mArray.keyType, mArray.valueType, SelectTerm.mSymbol);
		assert mArray.valueType == ReturnType.Array;
		select = new SelectTerm(mArray, mIndex);
	}

	@Override
	public ArraySelectTerm simplify() {
		final ArrayTerm mArray = select.getArray().simplify();
		final ExecutionTerm mIndex = select.getIndex().simplify();

		return new ArraySelectTerm(mArray, mIndex);
	}

	@Override
	public ArrayList<ExecutionTerm> getSubTerms() {
		return select.getSubTerms();
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		return select.toString(out, depth);
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof ArraySelectTerm)) {
			return false;
		}
		return select.equals(((ArraySelectTerm) b).select);
	}

	@Override
	public int hashCode() {
		return select.hashCode();
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		return select.getVariables();
	}

	@Override
	public Term toSMTTerm() {
		return select.toSMTTerm();
	}

	/*
	 * @Override public <subT extends Domain<subT>> ExecutionTerm<ArrayDomain<subKey, value>> replaceSubTerm(
	 * ExecutionTerm<subT> current, ExecutionTerm<subT> replacement) { return select.replaceSubTerm(current,
	 * replacement); }
	 */

	@Override
	public SMTArray evaluate(final ProgramState state) {
		return (SMTArray) select.evaluate(state);
	}
}
