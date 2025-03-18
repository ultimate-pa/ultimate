package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.SMTArray;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.ArrayDomain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.VariableTerm;

public class VariableArrayTerm extends ArrayTerm implements Variable {
	private final VariableTerm variableTerm;

	private VariableArrayTerm(final ReturnType mKeyType, final ReturnType mValueType,
			final VariableTerm iVariableTerm) {
		super(mKeyType, mValueType, SMTLIBConstants.ARRAY);
		assert mKeyType != ReturnType.Array;
		variableTerm = iVariableTerm;
	}

	public VariableArrayTerm(final ReturnType mKeyType, final ReturnType mValueType, final boolean mIsInVar,
			final boolean mIsOutVar, final boolean mIsAuxVar, final boolean mIsAssignable,
			final IProgramVar mProgramVar, final TermVariable mTermVar) {
		this(mKeyType, mValueType,
				new VariableTerm(mIsInVar, mIsOutVar, mIsAuxVar, mIsAssignable, mProgramVar, mTermVar));
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

		return castB.variableTerm.termvar.equals(variableTerm.termvar) && keyType.equals(castB.keyType)
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
		return variableTerm;
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
		return variableTerm.name;
	}

	@Override
	public TermVariable toSMTTerm(final Theory theory) {
		return Util.makeVariable(variableTerm.termvar, theory);
	}

	@Override
	public SMTArray evaluate(final ProgramState state) {
		return state.getArrayOf(variableTerm.programVar);
	}

	@Override
	public ArrayDomain<?, ?> getDomain() {
		return Util.constructFullDomain(variableTerm.termvar.getSort());
	}
}