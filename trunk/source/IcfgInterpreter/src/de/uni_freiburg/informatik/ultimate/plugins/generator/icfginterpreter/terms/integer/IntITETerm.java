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
		final IntegerTerm minusB = ite.mB.negate();
		final IntegerTerm minusC = ite.mC.negate();
		return new IntITETerm(ite.mCondition, minusB, minusC);
	}

	@Override
	public IntITETerm simplify() {
		return new IntITETerm(ite.mCondition.simplify(), ite.mB.simplify(), ite.mC.simplify());
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
		return new IntITETerm(replacement, ite.mB, ite.mC);
	}

	@Override
	public BooleanTerm getCondition() {
		return ite.mCondition;
	}

	@Override
	public Long evaluate(final ProgramState currentState, final ProgramState nextState) {
		return (Long) ite.evaluate(currentState, nextState);
	}

	@Override
	public String toCode() {
		return ite.toCode();
	}

	@Override
	protected IntITETerm replaceSubterms(final ExecutionTerm old, final ExecutionTerm replacement) {
		final BooleanTerm mA = ite.mCondition.replaceTerm(old, replacement);
		final IntegerTerm mB = ite.mB.replaceTerm(old, replacement);
		final IntegerTerm mC = ite.mC.replaceTerm(old, replacement);

		return new IntITETerm(new ITETerm<>(mA, mB, mC));
	}
}