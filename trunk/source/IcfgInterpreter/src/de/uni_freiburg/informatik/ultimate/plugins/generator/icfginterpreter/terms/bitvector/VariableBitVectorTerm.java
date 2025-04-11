package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bitvector;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datatypes.BitVector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BitVectorTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.VariableTerm;

public class VariableBitVectorTerm extends BitVectorTerm implements Variable {
	private final VariableTerm mVariableTerm;

	public VariableBitVectorTerm(final int length, final VariableTerm variableTerm) {
		super(SMTLIBConstants.BITVEC, length);
		mVariableTerm = variableTerm;
	}

	@Override
	public VariableTerm getVariableTerm() {
		return mVariableTerm;
	}

	@Override
	public VariableBitVectorTerm getTerm() {
		return this;
	}

	@Override
	public String getName() {
		return mVariableTerm.mName;
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof VariableBitVectorTerm)) {
			return false;
		}
		final VariableBitVectorTerm castB = (VariableBitVectorTerm) b;
		return mLength == castB.mLength && castB.mVariableTerm.mTermVar.equals(mVariableTerm.mTermVar);
	}

	@Override
	public int hashCode() {
		return 113 * 31 + getName().hashCode();
	}

	@Override
	public TermVariable toSMTTerm(final Theory theory) {
		return mVariableTerm.toSMTTerm(theory);
	}

	@Override
	public BitVectorTerm simplify() {
		return this;
	}

	@Override
	public BitVector evaluate(final ProgramState currentState, final ProgramState nextState) {
		return (mVariableTerm.isInVar ? currentState : nextState).getBitVectorOf(mVariableTerm.mProgramVar);
	}

	@Override
	public ArrayList<IntegerTerm> getSubTerms() {
		return new ArrayList<>();
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		final HashSet<Variable> out = new HashSet<>();
		out.add(this);
		return out;
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		return out.append(Util.getIndent(depth)).append(getName());
	}

	@Override
	public String toCode() {
		return mVariableTerm.toCode();
	}

	@Override
	protected VariableBitVectorTerm replaceSubterms(final ExecutionTerm old, final ExecutionTerm replacement) {
		return this;
	}

	@Override
	public VariableBitVectorTerm replaceTermVariable(final TermVariable termVar) {
		return new VariableBitVectorTerm(mLength, mVariableTerm.replaceTermVariable(termVar));
	}

	@Override
	public VariableBitVectorTerm replaceIProgramVar(final IProgramVar programVar) {
		return new VariableBitVectorTerm(mLength, mVariableTerm.replaceIProgramVar(programVar));
	}
}
