package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.VariableTerm;

public class VariableIntegerTerm extends IntegerTerm implements Variable {
	private final VariableTerm mVariableTerm;

	public VariableIntegerTerm(final VariableTerm variableTerm) {
		super(SMTLIBConstants.INT);
		mVariableTerm = variableTerm;
	}

	@Override
	public VariableIntegerTerm simplify() {
		return this;
	}

	@Override
	public NegationTerm negate() {
		return new NegationTerm(this);
	}

	@Override
	public ArrayList<IntegerTerm> getSubTerms() {
		return new ArrayList<>();
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		return out.append(Util.getIndent(depth)).append(getName());
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof VariableIntegerTerm)) {
			return false;
		}
		final VariableIntegerTerm castB = (VariableIntegerTerm) b;
		return castB.mVariableTerm.termvar.equals(mVariableTerm.termvar);
	}

	@Override
	public int hashCode() {
		return 97 * 31 + getName().hashCode();
	}

	@Override
	public VariableTerm getVariableTerm() {
		return mVariableTerm;
	}

	@Override
	public VariableIntegerTerm getTerm() {
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
		return mVariableTerm.toSMTTerm(theory);
	}

	@Override
	public Integer evaluate(final ProgramState currentState, final ProgramState nextState) {
		return (mVariableTerm.isInVar ? currentState : nextState).getIntOf(mVariableTerm.programVar);
	}

	@Override
	public String toCode() {
		return mVariableTerm.toCode();
	}
}