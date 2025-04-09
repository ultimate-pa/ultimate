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
 * Represents the unary function "-X"
 */
public class NegationTerm extends IntegerTerm {
	private final IntegerTerm mX;

	public NegationTerm(final IntegerTerm X) {
		super(SMTLIBConstants.MINUS);
		mX = X;
	}

	/**
	 * Returns "-X" with X simplified
	 */
	@Override
	public IntegerTerm simplify() {
		if (mX instanceof NegationTerm) {
			final NegationTerm xCast = (NegationTerm) mX;
			return xCast.mX.simplify();
		}
		return new NegationTerm(mX.simplify());
	}

	/**
	 * Returns "X"
	 */
	@Override
	public IntegerTerm negate() {
		return mX;
	}

	@Override
	public ArrayList<IntegerTerm> getSubTerms() {
		return new ArrayList<>(Arrays.asList(mX));
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		out.append(Util.getIndent(depth)).append("(-");
		mX.toString(out, 0);
		return out.append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof NegationTerm)) {
			return false;
		}
		final NegationTerm castB = (NegationTerm) b;
		return mX.equals(castB.mX);
	}

	@Override
	public int hashCode() {
		return 73 * 31 + mX.hashCode();
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
		return -mX.evaluate(currentState, nextState);
	}

	@Override
	public String toCode() {
		return "(-" + mX.toCode() + ")";
	}

	@Override
	protected NegationTerm replaceSubterms(final ExecutionTerm old, final ExecutionTerm replacement) {
		return new NegationTerm(mX.replaceTerm(old, replacement));
	}
}