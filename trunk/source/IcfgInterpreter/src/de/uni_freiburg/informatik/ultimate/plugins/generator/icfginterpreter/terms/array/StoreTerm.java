package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.SMTArray;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class StoreTerm extends ArrayTerm {
	private final ArrayTerm array;
	private final ExecutionTerm index;
	private final ExecutionTerm value;

	public StoreTerm(final ArrayTerm mArray, final ExecutionTerm mIndex, final ExecutionTerm mValue) {
		super(mArray.keyType, mArray.valueType, SMTLIBConstants.STORE);
		assert mArray.keyType == mIndex.returnType;
		assert mArray.valueType == mValue.returnType;
		array = mArray;
		index = mIndex;
		value = mValue;
	}

	@Override
	public StoreTerm simplify() {
		final ExecutionTerm newIndex = index.simplify();
		final ExecutionTerm newValue = value.simplify();
		// Store terms are also array terms, meaning we should pass on the simplify here.
		final ArrayTerm newArray = array.simplify();
		return new StoreTerm(newArray, newIndex, newValue);
	}

	@Override
	public ArrayList<ExecutionTerm> getSubTerms() {
		return Util.toList(array, index, value);
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		out.append(Util.getIndent(depth)).append("(store ");
		array.toString(out, 0).append(" ");
		index.toString(out, 0).append(" ");
		return value.toString(out, 0).append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof StoreTerm)) {
			return false;
		}
		final StoreTerm castB = (StoreTerm) b;

		return array.equals(castB.array) && index.equals(castB.index) && value.equals(castB.value);
	}

	@Override
	public int hashCode() {
		int result = 107 * 31 + array.hashCode();
		result = result * 31 + index.hashCode();
		return result * 31 + value.hashCode();
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		final HashSet<Variable> out = array.getVariables();
		out.addAll(index.getVariables());
		out.addAll(value.getVariables());
		return out;
	}

	@Override
	public Term toSMTTerm(final Theory theory) {
		return Util.makeTerm(mSymbol, theory, array.toSMTTerm(theory), index.toSMTTerm(theory),
				value.toSMTTerm(theory));
	}

	/*
	 * @Override public <subT extends Domain<subT>> ExecutionTerm<ArrayDomain<keyType, valueType>> replaceSubTerm(
	 * ExecutionTerm<subT> current, ExecutionTerm<subT> replacement) { ArrayTerm<keyType, valueType> mArray =
	 * array.equals(current) ? (ArrayTerm<keyType, valueType>) replacement : array; ExecutionTerm<keyType> mIndex =
	 * index.equals(current) ? (ExecutionTerm<keyType>) replacement : index; ExecutionTerm<valueType> mValue =
	 * value.equals(current) ? (ExecutionTerm<valueType>) replacement : value; return new StoreTerm<>(mArray, mIndex,
	 * mValue); }
	 */

	@Override
	public SMTArray evaluate(final ProgramState state) {
		final SMTArray mArray = array.evaluate(state);
		return mArray.store(index.evaluate(state), value.evaluate(state));
	}
}
