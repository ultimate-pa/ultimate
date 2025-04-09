package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

/**
 * Represents the binary function "X > Y"
 */
public class GreaterTerm extends BooleanTerm {
	private final IntegerTerm mX, mY;

	public GreaterTerm(final IntegerTerm X, final IntegerTerm Y) {
		super(SMTLIBConstants.GT);
		mX = X;
		mY = Y;
	}

	/**
	 * Returns "Y < X" with arguments simplified
	 */
	@Override
	public LessTerm simplify() {
		return new LessTerm(mY, mX).simplify();
	}

	/**
	 * Returns "X <= Y"
	 */
	@Override
	public BooleanTerm negate() {
		return new LessEqualTerm(mX, mY);
	}

	@Override
	public ArrayList<IntegerTerm> getSubTerms() {
		return Util.toList(mX, mY);
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		out.append(Util.getIndent(depth)).append("(");

		mX.toString(out, 0);
		out.append(" > ");
		mY.toString(out, 0);

		return out.append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof ExecutionTerm)) {
			return false;
		}

		return simplify().equals(((ExecutionTerm) b).simplify());
	}

	@Override
	public int hashCode() {
		final int result = 43 * 31 + mX.hashCode();
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
	public Boolean evaluate(final ProgramState currentState, final ProgramState nextState) {
		return mX.evaluate(currentState, nextState) > mY.evaluate(currentState, nextState);
	}

	@Override
	public String toCode() {
		return "(" + mX.toCode() + " > " + mY.toCode() + ")";
	}

	@Override
	protected GreaterTerm replaceSubterms(final ExecutionTerm old, final ExecutionTerm replacement) {
		final IntegerTerm X = mX.replaceTerm(old, replacement);
		final IntegerTerm Y = mY.replaceTerm(old, replacement);
		return new GreaterTerm(X, Y);
	}
}