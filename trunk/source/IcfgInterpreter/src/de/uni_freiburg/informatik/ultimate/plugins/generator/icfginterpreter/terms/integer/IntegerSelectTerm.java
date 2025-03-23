package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.SelectTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class IntegerSelectTerm extends IntegerTerm {
	private final SelectTerm select;

	public IntegerSelectTerm(final ArrayTerm mArray, final ExecutionTerm mIndex) {
		super(SelectTerm.mSymbol);
		assert mArray.valueType == ReturnType.Int;
		select = new SelectTerm(mArray, mIndex);
	}

	private IntegerSelectTerm(final SelectTerm mSelect) {
		super(SelectTerm.mSymbol);
		assert mSelect.getArray().valueType == ReturnType.Int;
		select = mSelect;
	}

	@Override
	public IntegerTerm negate() {
		return new NegationTerm(this);
	}

	@Override
	public IntegerSelectTerm simplify() {
		final ArrayTerm mArray = select.getArray().simplify();
		final ExecutionTerm mIndex = select.getIndex().simplify();

		return new IntegerSelectTerm(mArray, mIndex);
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
		if (!(b instanceof IntegerSelectTerm)) {
			return false;
		}
		return select.equals(((IntegerSelectTerm) b).select);
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
	public Term toSMTTerm(final Theory theory) {
		return select.toSMTTerm(theory);
	}

	/*
	 * @Override public <subT extends Domain<subT>> ExecutionTerm<IntegerDomain> replaceSubTerm(final
	 * ExecutionTerm<subT> current, final ExecutionTerm<subT> replacement) { return select.replaceSubTerm(current,
	 * replacement); }
	 */

	@Override
	public Integer evaluate(final ProgramState currentState, final ProgramState nextState) {
		return (int) select.evaluate(currentState, nextState);
	}
}