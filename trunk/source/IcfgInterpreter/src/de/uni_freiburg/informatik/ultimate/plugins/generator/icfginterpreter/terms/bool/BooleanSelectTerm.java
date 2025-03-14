package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.SelectTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class BooleanSelectTerm extends BooleanTerm {
	private final SelectTerm select;

	public BooleanSelectTerm(final ArrayTerm mArray, final ExecutionTerm mIndex) {
		super(SelectTerm.mSymbol);
		assert mArray.valueType == ReturnType.Boolean;
		select = new SelectTerm(mArray, mIndex);
	}

	private BooleanSelectTerm(final SelectTerm mSelect) {
		super(SelectTerm.mSymbol);
		assert mSelect.getArray().valueType == ReturnType.Boolean;
		select = mSelect;
	}

	@Override
	public BooleanTerm negate() {
		return new NotTerm(this);
	}

	@Override
	public BooleanSelectTerm simplify() {
		final ArrayTerm mArray = select.getArray().simplify();
		final ExecutionTerm mIndex = select.getIndex().simplify();

		return new BooleanSelectTerm(mArray, mIndex);
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
		if (!(b instanceof BooleanSelectTerm)) {
			return false;
		}
		return select.equals(((BooleanSelectTerm) b).select);
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
	 * @Override public <subT extends Domain<subT>> ExecutionTerm<BooleanDomain> replaceSubTerm(ExecutionTerm<subT>
	 * current, ExecutionTerm<subT> replacement) { return select.replaceSubTerm(current, replacement); }
	 */

	@Override
	public Boolean evaluate(final ProgramState state) {
		return (boolean) select.evaluate(state);
	}
}