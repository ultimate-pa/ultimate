package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

/**
 * Represents the unary function "-X"
 */
public class NegationTerm extends IntegerTerm {
	private final IntegerTerm X;

	public NegationTerm(final IntegerTerm mX) {
		super(SMTLIBConstants.MINUS);
		X = mX;
	}

	/**
	 * Returns "-X" with X simplified
	 */
	@Override
	public IntegerTerm simplify() {
		if (X instanceof NegationTerm) {
			final NegationTerm xCast = (NegationTerm) X;
			return xCast.X.simplify();
		}
		return new NegationTerm(X.simplify());
	}

	/**
	 * Returns "X"
	 */
	@Override
	public IntegerTerm negate() {
		return X;
	}

	@Override
	public ArrayList<IntegerTerm> getSubTerms() {
		return new ArrayList<>(Arrays.asList(X));
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		out.append(Util.getIndent(depth)).append("(-");
		X.toString(out, 0);
		return out.append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof NegationTerm)) {
			return false;
		}
		final NegationTerm castB = (NegationTerm) b;
		return X.equals(castB.X);
	}

	@Override
	public int hashCode() {
		return 73 * 31 + X.hashCode();
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		return X.getVariables();
	}

	@Override
	public Term toSMTTerm() {
		return Util.getTheory().term(mSymbol, X.toSMTTerm());
	}

	@Override
	public Integer evaluate(final ProgramState state) {
		return -X.evaluate(state);
	}
}