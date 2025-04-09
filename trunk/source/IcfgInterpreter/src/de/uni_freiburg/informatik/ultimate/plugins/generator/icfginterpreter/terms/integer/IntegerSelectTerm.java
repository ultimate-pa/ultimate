package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ReturnType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.SelectTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class IntegerSelectTerm extends IntegerTerm {
	private final SelectTerm mSelect;

	public IntegerSelectTerm(final ArrayTerm mArray, final ExecutionTerm mIndex) {
		super(SelectTerm.mSymbol);
		assert mArray.valueType == ReturnType.Int;
		mSelect = new SelectTerm(mArray, mIndex);
	}

	private IntegerSelectTerm(final SelectTerm select) {
		super(SelectTerm.mSymbol);
		assert select.getArray().valueType == ReturnType.Int;
		mSelect = select;
	}

	@Override
	public IntegerTerm negate() {
		return new NegationTerm(this);
	}

	@Override
	public IntegerSelectTerm simplify() {
		final ArrayTerm mArray = mSelect.getArray().simplify();
		final ExecutionTerm mIndex = mSelect.getIndex().simplify();

		return new IntegerSelectTerm(mArray, mIndex);
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
		if (!(b instanceof IntegerSelectTerm)) {
			return false;
		}
		return mSelect.equals(((IntegerSelectTerm) b).mSelect);
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
	public Long evaluate(final ProgramState currentState, final ProgramState nextState) {
		return (Long) mSelect.evaluate(currentState, nextState);
	}

	@Override
	public String toCode() {
		return "((long) " + mSelect.toCode() + ")";
	}

	@Override
	protected IntegerSelectTerm replaceSubterms(final ExecutionTerm old, final ExecutionTerm replacement) {
		return new IntegerSelectTerm(mSelect.replaceTerm(old, replacement));
	}
}