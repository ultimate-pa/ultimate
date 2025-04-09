package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.ITETerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class BoolITETerm extends BooleanTerm {
	private final ITETerm<BooleanTerm> ite;

	public BoolITETerm(final BooleanTerm condition, final BooleanTerm ifTerm, final BooleanTerm elseTerm) {
		super(ITETerm.mSymbol);
		ite = new ITETerm<>(condition, ifTerm, elseTerm);
	}

	public BoolITETerm(final ITETerm<BooleanTerm> mITE) {
		super(ITETerm.mSymbol);
		ite = mITE;
	}

	@Override
	public BooleanTerm negate() {
		final BooleanTerm notB = ite.mB.negate();
		final BooleanTerm notC = ite.mC.negate();
		return new BoolITETerm(ite.mCondition, notB, notC);
	}

	/**
	 * @return (A and B) or ((not A) and C)
	 */
	@Override
	public OrTerm simplify() {
		final AndTerm AAndB = new AndTerm(ite.mCondition, ite.mB);
		final AndTerm NotAAndC = new AndTerm(ite.mCondition.negate(), ite.mC);
		return new OrTerm(AAndB, NotAAndC);
	}

	@Override
	public ArrayList<BooleanTerm> getSubTerms() {
		return Util.toList(ite.mCondition, ite.mB, ite.mC);
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		return ite.toString(out, depth);
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof BoolITETerm)) {
			return false;
		}
		return ite.equals(((BoolITETerm) b).ite);
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
	public Boolean evaluate(final ProgramState currentState, final ProgramState nextState) {
		return (Boolean) ite.evaluate(currentState, nextState);
	}

	@Override
	public String toCode() {
		return ite.toCode();
	}

	@Override
	protected BoolITETerm replaceSubterms(final ExecutionTerm old, final ExecutionTerm replacement) {
		final BooleanTerm mA = ite.mCondition.replaceTerm(old, replacement);
		final BooleanTerm mB = ite.mB.replaceTerm(old, replacement);
		final BooleanTerm mC = ite.mC.replaceTerm(old, replacement);

		return new BoolITETerm(new ITETerm<>(mA, mB, mC));
	}
}