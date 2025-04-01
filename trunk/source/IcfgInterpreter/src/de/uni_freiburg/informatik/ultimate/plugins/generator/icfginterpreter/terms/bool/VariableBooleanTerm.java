package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.VariableTerm;

public class VariableBooleanTerm extends BooleanTerm implements Variable {
	private final VariableTerm mVariableTerm;

	public VariableBooleanTerm(final VariableTerm variableTerm) {
		super(SMTLIBConstants.BOOL);
		mVariableTerm = variableTerm;
	}

	@Override
	public VariableBooleanTerm simplify() {
		return this;
	}

	@Override
	public NotTerm negate() {
		return new NotTerm(this);
	}

	@Override
	public ArrayList<BooleanTerm> getSubTerms() {
		return new ArrayList<>();
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		return out.append(Util.getIndent(depth)).append(getName());
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof VariableBooleanTerm)) {
			return false;
		}
		final VariableBooleanTerm castB = (VariableBooleanTerm) b;
		return castB.mVariableTerm.termvar.equals(mVariableTerm.termvar);
	}

	@Override
	public int hashCode() {
		return 89 * 31 + getName().hashCode();
	}

	@Override
	public VariableTerm getVariableTerm() {
		return mVariableTerm;
	}

	@Override
	public VariableBooleanTerm getTerm() {
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
	public Boolean evaluate(final ProgramState currentState, final ProgramState nextState) {
		return (mVariableTerm.isInVar ? currentState : nextState).getBoolOf(mVariableTerm.programVar);
	}

	@Override
	public String toCode() {
		return mVariableTerm.toCode();
	}
}