package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic;

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
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array.ArraySelectTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.BooleanSelectTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.IntegerSelectTerm;

public class SelectTerm {
	private final ArrayTerm array;
	private final ExecutionTerm index;
	public final static String mSymbol = SMTLIBConstants.SELECT;

	public SelectTerm(final ArrayTerm mArray, final ExecutionTerm mIndex) {
		assert mArray.keyType == mIndex.returnType;
		array = mArray;
		index = mIndex;
	}

	public ArrayList<ExecutionTerm> getSubTerms() {
		return Util.toList(array, index);
	}

	public ArrayTerm getArray() {
		return array;
	}

	public ExecutionTerm getIndex() {
		return index;
	}

	public StringBuilder toString(final StringBuilder out, final int depth) {
		out.append(Util.getIndent(depth)).append("(select ");
		array.toString(out, 0).append(" ");
		return index.toString(out, 0).append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof SelectTerm)) {
			return false;
		}
		final SelectTerm castB = (SelectTerm) b;

		return array.equals(castB.array) && index.equals(castB.index);
	}

	@Override
	public int hashCode() {
		final int result = 109 * 31 + array.hashCode();
		return result * 31 + index.hashCode();
	}

	public HashSet<Variable> getVariables() {
		final HashSet<Variable> out = array.getVariables();
		out.addAll(index.getVariables());
		return out;
	}

	public static ExecutionTerm getSelectTerm(final ArrayTerm mArray, final ExecutionTerm index) {
		switch (mArray.valueType) {
		case Array:
			return new ArraySelectTerm(mArray, index);
		case BitVector: // TODO
			break;
		case Boolean:
			return new BooleanSelectTerm(mArray, index);
		case Int:
			return new IntegerSelectTerm(mArray, index);
		}
		return null;
	}

	public Term toSMTTerm(final Theory theory) {
		return Util.makeTerm(mSymbol, theory, array.toSMTTerm(theory), index.toSMTTerm(theory));
	}

	/*
	 * @Override public <subT extends Domain<subT>> ExecutionTerm<valueType> replaceSubTerm(ExecutionTerm<subT> current,
	 * ExecutionTerm<subT> replacement) { ArrayTerm<keyType, valueType> mArray = array.equals(current) ?
	 * (ArrayTerm<keyType, valueType>) replacement : array; ExecutionTerm<keyType> mIndex = index.equals(current) ?
	 * (ExecutionTerm<keyType>) replacement : index; return new SelectTerm<>(mArray, mIndex); }
	 */

	public Object evaluate(final ProgramState state) {
		final SMTArray mArray = array.evaluate(state);
		return mArray.select(index.evaluate(state));
	}
}
