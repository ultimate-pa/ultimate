package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.SMTArray;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.ITETerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class ArrayITETerm extends ArrayTerm {
	private final ITETerm<ArrayTerm> ite;

	public ArrayITETerm(final BooleanTerm condition, final ArrayTerm ifTerm, final ArrayTerm elseTerm) {
		super(ifTerm.keyType, ifTerm.valueType, ITETerm.mSymbol);
		assert ifTerm.keyType == elseTerm.keyType && ifTerm.valueType == elseTerm.valueType;
		ite = new ITETerm<>(condition, ifTerm, elseTerm);
	}

	private ArrayITETerm(final ITETerm<ArrayTerm> mITE) {
		super(mITE.B.keyType, mITE.B.valueType, ITETerm.mSymbol);
		ite = mITE;
	}

	@Override
	public ArrayITETerm simplify() {
		return new ArrayITETerm(ite.A.simplify(), ite.B.simplify(), ite.C.simplify());
	}

	@Override
	public ArrayList<ExecutionTerm> getSubTerms() {
		return ite.getSubTerms();
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		return ite.toString(out, depth);
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof ArrayITETerm)) {
			return false;
		}
		return ite.equals(((ArrayITETerm) b).ite);
	}

	@Override
	public int hashCode() {
		return ite.hashCode();
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		return ite.getVariables();
	}

	@Override
	public Term toSMTTerm() {
		return ite.toSMTTerm();
	}

	/*
	 * @Override public <subT extends Domain<subT>> ExecutionTerm<ArrayDomain<keyType, valueType>> replaceSubTerm(
	 * ExecutionTerm<subT> current, ExecutionTerm<subT> replacement) { return new
	 * ArrayITETerm<>(ite.replaceSubTerm(current, replacement)); }
	 */

	@Override
	public SMTArray evaluate(final ProgramState state) {
		return (SMTArray) ite.evaluate(state);
	}
}