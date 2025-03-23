package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bitvector;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.BitVector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BitVectorTerm;
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
		return mVariableTerm.name;
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof VariableBitVectorTerm)) {
			return false;
		}
		final VariableBitVectorTerm castB = (VariableBitVectorTerm) b;
		return mLength == castB.mLength && castB.mVariableTerm.termvar.equals(mVariableTerm.termvar);
	}

	@Override
	public int hashCode() {
		return 113 * 31 + getName().hashCode();
	}

	@Override
	public TermVariable toSMTTerm(final Theory theory) {
		return Util.makeVariable(mVariableTerm.termvar, theory);
	}

	@Override
	public BitVectorTerm simplify() {
		return this;
	}

	@Override
	public BitVector evaluate(final ProgramState currentState, final ProgramState nextState) {
		return (mVariableTerm.isInVar ? currentState : nextState).getBitVectorOf(mVariableTerm.programVar);
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
}
