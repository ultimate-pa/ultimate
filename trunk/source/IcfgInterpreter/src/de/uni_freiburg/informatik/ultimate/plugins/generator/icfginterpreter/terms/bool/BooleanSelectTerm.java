package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ReturnType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.SelectTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class BooleanSelectTerm extends BooleanTerm {
	private final SelectTerm mSelect;

	public BooleanSelectTerm(final ArrayTerm mArray, final ExecutionTerm mIndex) {
		super(SelectTerm.mSymbol);
		assert mArray.valueType == ReturnType.Boolean;
		mSelect = new SelectTerm(mArray, mIndex);
	}

	private BooleanSelectTerm(final SelectTerm select) {
		super(SelectTerm.mSymbol);
		assert select.getArray().valueType == ReturnType.Boolean;
		mSelect = select;
	}

	@Override
	public BooleanTerm negate() {
		return new NotTerm(this);
	}

	@Override
	public BooleanSelectTerm simplify() {
		final ArrayTerm mArray = mSelect.getArray().simplify();
		final ExecutionTerm mIndex = mSelect.getIndex().simplify();

		return new BooleanSelectTerm(mArray, mIndex);
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
		if (!(b instanceof BooleanSelectTerm)) {
			return false;
		}
		return mSelect.equals(((BooleanSelectTerm) b).mSelect);
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
	public Boolean evaluate(final ProgramState currentState, final ProgramState nextState) {
		return (boolean) mSelect.evaluate(currentState, nextState);
	}

	@Override
	public String toCode() {
		return "((boolean) " + mSelect.toCode() + ")";
	}

	@Override
	protected BooleanSelectTerm replaceSubterms(final ExecutionTerm old, final ExecutionTerm replacement) {
		return new BooleanSelectTerm(mSelect.replaceTerm(old, replacement));
	}
}