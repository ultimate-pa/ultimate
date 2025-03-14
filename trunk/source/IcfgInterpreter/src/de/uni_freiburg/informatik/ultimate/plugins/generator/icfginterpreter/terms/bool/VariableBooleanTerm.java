package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.VariableTerm;

public class VariableBooleanTerm extends BooleanTerm implements Variable {
	private final VariableTerm variableTerm;

	public VariableBooleanTerm(final VariableTerm iVariableTerm) {
		super(SMTLIBConstants.BOOL);
		variableTerm = iVariableTerm;
	}

	public VariableBooleanTerm(final boolean mIsInVar, final boolean mIsOutVar, final boolean mIsAuxVar,
			final boolean mIsAssignable, final IProgramVar mProgramVar, final TermVariable mTermVar) {
		this(new VariableTerm(mIsInVar, mIsOutVar, mIsAuxVar, mIsAssignable, mProgramVar, mTermVar));
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
		return castB.variableTerm.termvar.equals(variableTerm.termvar);
	}

	@Override
	public int hashCode() {
		return 89 * 31 + getName().hashCode();
	}

	@Override
	public VariableTerm getVariableTerm() {
		return variableTerm;
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
		return variableTerm.name;
	}

	@Override
	public Term toSMTTerm() {
		return variableTerm.termvar;
	}

	@Override
	public Boolean evaluate(final ProgramState state) {
		return state.getBoolOf(variableTerm.programVar);
	}
}