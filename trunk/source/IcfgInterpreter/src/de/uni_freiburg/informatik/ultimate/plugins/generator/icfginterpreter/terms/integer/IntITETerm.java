package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.ITETerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.ITETerm.ITE;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class IntITETerm extends IntegerTerm implements ITE {
	private final ITETerm<IntegerTerm> ite;

	public IntITETerm(final BooleanTerm condition, final IntegerTerm ifTerm, final IntegerTerm elseTerm) {
		super(ITETerm.mSymbol);
		ite = new ITETerm<>(condition, ifTerm, elseTerm);
	}

	private IntITETerm(final ITETerm<IntegerTerm> mITE) {
		super(ITETerm.mSymbol);
		ite = mITE;
	}

	/**
	 * @return if A then (-B) else (-C)
	 */
	@Override
	public IntITETerm negate() {
		final IntegerTerm minusB = ite.B.negate();
		final IntegerTerm minusC = ite.C.negate();
		return new IntITETerm(ite.A, minusB, minusC);
	}

	@Override
	public IntITETerm simplify() {
		return new IntITETerm(ite.A.simplify(), ite.B.simplify(), ite.C.simplify());
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
		if (!(b instanceof IntITETerm)) {
			return false;
		}
		return ite.equals(((IntITETerm) b).ite);
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
	public Term toSMTTerm(final Theory theory) {
		return ite.toSMTTerm(theory);
	}

	@Override
	public IntITETerm replaceCondition(final BooleanTerm replacement) {
		return new IntITETerm(replacement, ite.B, ite.C);
	}

	@Override
	public BooleanTerm getCondition() {
		return ite.A;
	}

	/*
	 * @Override public <subT extends Domain<subT>> ExecutionTerm<IntegerDomain> replaceSubTerm(ExecutionTerm<subT>
	 * current, ExecutionTerm<subT> replacement) { return new IntITETerm(ite.replaceSubTerm(current, replacement)); }
	 */

	@Override
	public Integer evaluate(final ProgramState currentState, final ProgramState nextState) {
		return (int) ite.evaluate(currentState, nextState);
	}

	@Override
	public String toCode() {
		return ite.toCode();
	}
}