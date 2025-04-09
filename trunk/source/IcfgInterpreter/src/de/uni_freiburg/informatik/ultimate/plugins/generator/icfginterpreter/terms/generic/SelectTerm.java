package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datatypes.SMTArray;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array.ArraySelectTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.BooleanSelectTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.IntegerSelectTerm;

public class SelectTerm {
	private final ArrayTerm mArray;
	private final ExecutionTerm mIndex;
	public final static String mSymbol = SMTLIBConstants.SELECT;

	public SelectTerm(final ArrayTerm array, final ExecutionTerm index) {
		assert array.keyType == index.returnType;
		mArray = array;
		mIndex = index;
	}

	public ArrayList<ExecutionTerm> getSubTerms() {
		return Util.toList(mArray, mIndex);
	}

	public ArrayTerm getArray() {
		return mArray;
	}

	public ExecutionTerm getIndex() {
		return mIndex;
	}

	public StringBuilder toString(final StringBuilder out, final int depth) {
		out.append(Util.getIndent(depth)).append("(select ");
		mArray.toString(out, 0).append(" ");
		return mIndex.toString(out, 0).append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof SelectTerm)) {
			return false;
		}
		final SelectTerm castB = (SelectTerm) b;

		return mArray.equals(castB.mArray) && mIndex.equals(castB.mIndex);
	}

	@Override
	public int hashCode() {
		final int result = 109 * 31 + mArray.hashCode();
		return result * 31 + mIndex.hashCode();
	}

	public HashSet<Variable> getVariables() {
		final HashSet<Variable> out = mArray.getVariables();
		out.addAll(mIndex.getVariables());
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
		return Util.makeTerm(mSymbol, theory, mArray.toSMTTerm(theory), mIndex.toSMTTerm(theory));
	}

	public Object evaluate(final ProgramState currentState, final ProgramState nextState) {
		final SMTArray array = mArray.evaluate(currentState, nextState);
		return array.select(mIndex.evaluate(currentState, nextState), currentState.getNDC());
	}

	public String toCode() {
		return mArray.toCode() + ".select(" + mIndex.toCode() + ", nextState.getNDC())";
	}

	public SelectTerm replaceTerm(final ExecutionTerm old, final ExecutionTerm replacement) {
		final ArrayTerm array = mArray.replaceTerm(old, replacement);
		final ExecutionTerm index = mIndex.replaceTerm(old, replacement);

		return new SelectTerm(array, index);
	}
}
