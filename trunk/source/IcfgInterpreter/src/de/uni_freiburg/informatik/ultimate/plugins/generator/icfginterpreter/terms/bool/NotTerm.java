package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

/**
 * Represents the unary boolean function "not(A)"
 */
public class NotTerm extends BooleanTerm {
	private final BooleanTerm A;

	public NotTerm(final BooleanTerm mSubterm) {
		super(SMTLIBConstants.NOT);
		A = mSubterm;
	}

	/**
	 * Returns its sub-term unchanged. <br>
	 * Not(A).negate() => A
	 */
	@Override
	public BooleanTerm negate() {
		return A;
	}

	/**
	 * Returns its negated and simplified sub-term.
	 */
	@Override
	public BooleanTerm simplify() {
		if (A instanceof NotTerm) {
			return A.simplify();
		}
		final BooleanTerm mA = A.simplify();
		final BooleanTerm notA = mA.negate();
		if (!(notA instanceof NotTerm)) {
			return notA.simplify();
		}
		return new NotTerm(mA);
	}

	@Override
	public ArrayList<BooleanTerm> getSubTerms() {
		return new ArrayList<>(Arrays.asList(A));
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		out.append(Util.getIndent(depth)).append("not(\n");
		A.toString(out, depth + 1);
		return out.append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof NotTerm)) {
			return false;
		}
		final NotTerm castB = (NotTerm) b;
		return A.equals(castB.A);
	}

	@Override
	public int hashCode() {
		return 79 * 31 + A.hashCode();
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		return A.getVariables();
	}

	@Override
	public Boolean evaluate(final ProgramState state) {
		return !A.evaluate(state);
	}

	@Override
	public Term toSMTTerm(final Theory theory) {
		return Util.makeTerm(mSymbol, theory, A.toSMTTerm(theory));
	}
}