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
 * Represents the binary function "X // Y"
 */
public class DivisionTerm extends IntegerTerm {
	private final IntegerTerm X;
	private final IntegerTerm Y;

	public DivisionTerm(final IntegerTerm mX, final IntegerTerm mY) {
		super(SMTLIBConstants.DIV);
		X = mX;
		Y = mY;
	}

	/**
	 * Returns "X // Y" with X and Y simplified
	 */
	@Override
	public IntegerTerm simplify() {
		return new DivisionTerm(X.simplify(), Y.simplify());
	}

	@Override
	public IntegerTerm negate() {
		return new NegationTerm(this);
	}

	@Override
	public ArrayList<IntegerTerm> getSubTerms() {
		return new ArrayList<>(Arrays.asList(X, Y));
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		out.append(Util.getIndent(depth)).append("(");
		X.toString(out, 0);
		out.append(" / ");
		Y.toString(out, 0);
		return out.append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof DivisionTerm)) {
			return false;
		}
		final DivisionTerm castB = (DivisionTerm) b;
		return X.equals(castB.X) && X.equals(castB.Y);
	}

	@Override
	public int hashCode() {
		final int result = 29 * 31 + X.hashCode();
		return result * 31 + Y.hashCode();
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		final HashSet<Variable> out = X.getVariables();
		out.addAll(Y.getVariables());
		return out;
	}

	/*
	 * @Override public IntegerDomain evaluate(final HashMap<Variable<?>, Domain<?>> variableDomains) { return
	 * X.evaluate(variableDomains).divide(Y.evaluate(variableDomains)); }
	 */

	@Override
	public Term toSMTTerm(final Theory theory) {
		return Util.makeTerm(mSymbol, theory, X.toSMTTerm(theory), Y.toSMTTerm(theory));
	}

	@Override
	public Integer evaluate(final ProgramState currentState, final ProgramState nextState) {
		final int a = X.evaluate(currentState, nextState);
		final int b = Y.evaluate(currentState, nextState);

		return Util.SMTDiv(a, b);
	}
}