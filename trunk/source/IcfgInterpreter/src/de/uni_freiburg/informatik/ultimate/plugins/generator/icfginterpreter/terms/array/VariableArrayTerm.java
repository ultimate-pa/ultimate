package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.SMTArray;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.VariableTerm;

public class VariableArrayTerm extends ArrayTerm implements Variable {
	private final VariableTerm mVariableTerm;

	public VariableArrayTerm(final ReturnType mKeyType, final ReturnType mValueType, final VariableTerm variableTerm) {
		super(mKeyType, mValueType, SMTLIBConstants.ARRAY);
		assert mKeyType != ReturnType.Array;
		mVariableTerm = variableTerm;
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		return out.append(Util.getIndent(depth)).append(getName());
	}

	@Override
	public VariableArrayTerm simplify() {
		return this;
	}

	@Override
	public ArrayList<ArrayTerm> getSubTerms() {
		return new ArrayList<>();
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof VariableArrayTerm)) {
			return false;
		}
		final VariableArrayTerm castB = (VariableArrayTerm) b;

		return castB.mVariableTerm.termvar.equals(mVariableTerm.termvar) && keyType.equals(castB.keyType)
				&& valueType.equals(castB.valueType);
	}

	@Override
	public int hashCode() {
		int result = 103 * 31 + getName().hashCode();
		result = result * 31 + keyType.hashCode();
		return result * 31 + valueType.hashCode();
	}

	@Override
	public VariableTerm getVariableTerm() {
		return mVariableTerm;
	}

	@Override
	public VariableArrayTerm getTerm() {
		return this;
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		final HashSet<Variable> out = new HashSet<>();
		out.add(this);
		return out;
	}

	@Override
	public String getName() {
		return mVariableTerm.name;
	}

	@Override
	public TermVariable toSMTTerm(final Theory theory) {
		return Util.makeVariable(mVariableTerm.termvar, theory);
	}

	@Override
	public SMTArray evaluate(final ProgramState currentState, final ProgramState nextState) {
		return (mVariableTerm.isInVar ? currentState : nextState).getArrayOf(mVariableTerm.programVar);
	}
}