package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

/**
 * Represents the unary function "absolute(X)"
 */
public class AbsoluteTerm extends IntegerTerm {
	protected final IntegerTerm X;

	public AbsoluteTerm(final IntegerTerm mX) {
		super(SMTLIBConstants.ABS);
		X = mX;
	}

	/**
	 * Returns "absolute(X)" with X simplified
	 */
	@Override
	public IntegerTerm simplify() {
		return new AbsoluteTerm(X.simplify());
	}

	@Override
	public IntegerTerm negate() {
		return new NegationTerm(this);
	}

	@Override
	public ArrayList<IntegerTerm> getSubTerms() {
		return new ArrayList<>(Arrays.asList(X));
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		out.append(Util.getIndent(depth)).append("abs(");
		X.toString(out, 0);
		return out.append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof AbsoluteTerm)) {
			return false;
		}
		final AbsoluteTerm castB = (AbsoluteTerm) b;
		return X.equals(castB.X);
	}

	@Override
	public int hashCode() {
		return 7 * 31 + X.hashCode();
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		return X.getVariables();
	}

	@Override
	public Term toSMTTerm(final Theory theory) {
		return Util.makeTerm(mSymbol, theory, X.toSMTTerm(theory));
	}

	/*
	 * @Override public <subT extends Domain<subT>> ExecutionTerm replaceSubTerm(ExecutionTerm<subT> current,
	 * ExecutionTerm<subT> replacement) { if(X.equals(current)) { return new AbsoluteTerm((IntegerTerm) replacement); }
	 * return this; }
	 */

	@Override
	public Integer evaluate(final ProgramState state) {
		return Math.abs(X.evaluate(state));
	}
}