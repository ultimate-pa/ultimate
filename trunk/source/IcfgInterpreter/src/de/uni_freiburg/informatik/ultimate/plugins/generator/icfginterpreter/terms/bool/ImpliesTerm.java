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
 * Represents the binary boolean function "A -> B"
 */
public class ImpliesTerm extends BooleanTerm {
	private final BooleanTerm A;
	private final BooleanTerm B;

	public ImpliesTerm(final BooleanTerm mA, final BooleanTerm mB) {
		super(SMTLIBConstants.IMPLIES);
		A = mA;
		B = mB;
	}

	/**
	 * Returns the logically equivalent "not(A) or B" after simplifying it.
	 */
	@Override
	public BooleanTerm simplify() {
		return new OrTerm(A.negate(), B).simplify();
	}

	/**
	 * Returns the negation "A and not(B)"
	 */
	@Override
	public BooleanTerm negate() {
		return new AndTerm(A, B.negate());
	}

	@Override
	public ArrayList<BooleanTerm> getSubTerms() {
		return new ArrayList<>(Arrays.asList(A, B));
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		final String indent = Util.getIndent(depth);
		out.append(indent).append("->(\n");
		A.toString(out, depth + 1);
		out.append(",\n");
		B.toString(out, depth + 1).append("\n");
		return out.append(indent).append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof ImpliesTerm)) {
			return false;
		}
		final ImpliesTerm castB = (ImpliesTerm) b;
		return A.equals(castB.A) && B.equals(castB.B);
	}

	@Override
	public int hashCode() {
		final int result = 59 * 31 + A.hashCode();
		return result * 31 + B.hashCode();
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		final HashSet<Variable> out = A.getVariables();
		out.addAll(B.getVariables());
		return out;
	}

	@Override
	public Term toSMTTerm(final Theory theory) {
		return Util.makeTerm(mSymbol, theory, A.toSMTTerm(theory), B.toSMTTerm(theory));
	}

	/*
	 * @Override public <subT extends Domain<subT>> ExecutionTerm<BooleanDomain> replaceSubTerm(final
	 * ExecutionTerm<subT> current, final ExecutionTerm<subT> replacement) { final BooleanTerm mA = A.equals(current) ?
	 * (BooleanTerm) replacement : A; final BooleanTerm mB = B.equals(current) ? (BooleanTerm) replacement : B; return
	 * new ImpliesTerm(mA, mB); }
	 */

	@Override
	public Boolean evaluate(final ProgramState currentState, final ProgramState nextState) {
		return (!A.evaluate(currentState, nextState)) || B.evaluate(currentState, nextState);
	}
}