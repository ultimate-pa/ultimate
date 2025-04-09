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
 * Represents the binary function "X // Y"
 */
public class DivisionTerm extends IntegerTerm {
	private final IntegerTerm mX;
	private final IntegerTerm mY;

	public DivisionTerm(final IntegerTerm X, final IntegerTerm Y) {
		super(SMTLIBConstants.DIV);
		mX = X;
		mY = Y;
	}

	/**
	 * Returns "X // Y" with X and Y simplified
	 */
	@Override
	public IntegerTerm simplify() {
		return new DivisionTerm(mX.simplify(), mY.simplify());
	}

	@Override
	public IntegerTerm negate() {
		return new NegationTerm(this);
	}

	@Override
	public ArrayList<IntegerTerm> getSubTerms() {
		return new ArrayList<>(Arrays.asList(mX, mY));
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		out.append(Util.getIndent(depth)).append("(");
		mX.toString(out, 0);
		out.append(" / ");
		mY.toString(out, 0);
		return out.append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof DivisionTerm)) {
			return false;
		}
		final DivisionTerm castB = (DivisionTerm) b;
		return mX.equals(castB.mX) && mY.equals(castB.mY);
	}

	@Override
	public int hashCode() {
		final int result = 29 * 31 + mX.hashCode();
		return result * 31 + mY.hashCode();
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		final HashSet<Variable> out = mX.getVariables();
		out.addAll(mY.getVariables());
		return out;
	}

	@Override
	public Term toSMTTerm(final Theory theory) {
		return Util.makeTerm(mSymbol, theory, mX.toSMTTerm(theory), mY.toSMTTerm(theory));
	}

	@Override
	public Long evaluate(final ProgramState currentState, final ProgramState nextState) {
		final Long a = mX.evaluate(currentState, nextState);
		final Long b = mY.evaluate(currentState, nextState);

		return Util.SMTDiv(a, b);
	}

	@Override
	public String toCode() {
		return "Util.SMTDiv(" + mX.toCode() + ", " + mY.toCode() + ")";
	}

	@Override
	protected DivisionTerm replaceSubterms(final ExecutionTerm old, final ExecutionTerm replacement) {
		final IntegerTerm X = mX.replaceTerm(old, replacement);
		final IntegerTerm Y = mY.replaceTerm(old, replacement);
		return new DivisionTerm(X, Y);
	}
}