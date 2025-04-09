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
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

/**
 * Represents the binary boolean function "A -> B"
 */
public class ImpliesTerm extends BooleanTerm {
	private final BooleanTerm mA;
	private final BooleanTerm mB;

	public ImpliesTerm(final BooleanTerm A, final BooleanTerm B) {
		super(SMTLIBConstants.IMPLIES);
		mA = A;
		mB = B;
	}

	/**
	 * Returns the logically equivalent "not(A) or B" after simplifying it.
	 */
	@Override
	public BooleanTerm simplify() {
		return new OrTerm(mA.negate(), mB).simplify();
	}

	/**
	 * Returns the negation "A and not(B)"
	 */
	@Override
	public BooleanTerm negate() {
		return new AndTerm(mA, mB.negate());
	}

	@Override
	public ArrayList<BooleanTerm> getSubTerms() {
		return new ArrayList<>(Arrays.asList(mA, mB));
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		final String indent = Util.getIndent(depth);
		out.append(indent).append("->(\n");
		mA.toString(out, depth + 1);
		out.append(",\n");
		mB.toString(out, depth + 1).append("\n");
		return out.append(indent).append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof ImpliesTerm)) {
			return false;
		}
		final ImpliesTerm castB = (ImpliesTerm) b;
		return mA.equals(castB.mA) && mB.equals(castB.mB);
	}

	@Override
	public int hashCode() {
		final int result = 59 * 31 + mA.hashCode();
		return result * 31 + mB.hashCode();
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		final HashSet<Variable> out = mA.getVariables();
		out.addAll(mB.getVariables());
		return out;
	}

	@Override
	public Term toSMTTerm(final Theory theory) {
		return Util.makeTerm(mSymbol, theory, mA.toSMTTerm(theory), mB.toSMTTerm(theory));
	}

	@Override
	public Boolean evaluate(final ProgramState currentState, final ProgramState nextState) {
		return (!mA.evaluate(currentState, nextState)) || mB.evaluate(currentState, nextState);
	}

	@Override
	public String toCode() {
		return "((!" + mA.toCode() + ") || " + mB.toCode() + ")";
	}

	@Override
	protected ImpliesTerm replaceSubterms(final ExecutionTerm old, final ExecutionTerm replacement) {
		final BooleanTerm A = mA.replaceTerm(old, replacement);
		final BooleanTerm B = mB.replaceTerm(old, replacement);
		return new ImpliesTerm(A, B);
	}
}