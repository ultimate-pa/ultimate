package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

/**
 * Represents the unary function "absolute(X)"
 */
public class AbsoluteTerm extends IntegerTerm {
	protected final IntegerTerm mX;

	public AbsoluteTerm(final IntegerTerm X) {
		super(SMTLIBConstants.ABS);
		mX = X;
	}

	/**
	 * Returns "absolute(X)" with X simplified
	 */
	@Override
	public IntegerTerm simplify() {
		return new AbsoluteTerm(mX.simplify());
	}

	@Override
	public IntegerTerm negate() {
		return new NegationTerm(this);
	}

	@Override
	public ArrayList<IntegerTerm> getSubTerms() {
		return new ArrayList<>(Arrays.asList(mX));
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		out.append(Util.getIndent(depth)).append("abs(");
		mX.toString(out, 0);
		return out.append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof AbsoluteTerm)) {
			return false;
		}
		final AbsoluteTerm castB = (AbsoluteTerm) b;
		return mX.equals(castB.mX);
	}

	@Override
	public int hashCode() {
		return 7 * 31 + mX.hashCode();
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		return mX.getVariables();
	}

	@Override
	public Term toSMTTerm(final Theory theory) {
		return Util.makeTerm(mSymbol, theory, mX.toSMTTerm(theory));
	}

	@Override
	public Long evaluate(final ProgramState currentState, final ProgramState nextState) {
		return Math.abs(mX.evaluate(currentState, nextState));
	}

	@Override
	public String toCode() {
		return "Math.abs(" + mX.toCode() + ")";
	}

	@Override
	protected AbsoluteTerm replaceSubterms(final ExecutionTerm old, final ExecutionTerm replacement) {
		return new AbsoluteTerm(mX.replaceTerm(old, replacement));
	}
}