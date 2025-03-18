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
 * Represents the binary boolean function "A xor B"
 */
public class XorTerm extends BooleanTerm {
	private final BooleanTerm A;
	private final BooleanTerm B;

	public XorTerm(final BooleanTerm mA, final BooleanTerm mB) {
		super(SMTLIBConstants.XOR);
		A = mA;
		B = mB;
	}

	/**
	 * Returns the logically equivalent "(not(A) and B) or (A and not(B))" after simplifying it.
	 */
	@Override
	public BooleanTerm simplify() {
		final BooleanTerm notAandB = new AndTerm(A.negate(), B);

		final BooleanTerm AandnotB = new AndTerm(A, B.negate());

		return new OrTerm(notAandB, AandnotB).simplify();
	}

	/**
	 * Returns "(A and B) or (not(A) and not(B))"
	 */
	@Override
	public BooleanTerm negate() {
		final BooleanTerm AandB = new AndTerm(A, B);

		final BooleanTerm notAandnotB = new AndTerm(A.negate(), B.negate());
		return new OrTerm(AandB, notAandnotB);
	}

	@Override
	public ArrayList<BooleanTerm> getSubTerms() {
		return new ArrayList<>(Arrays.asList(A, B));
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		final String indent = Util.getIndent(depth);
		out.append(indent).append("xor(\n");
		A.toString(out, depth + 1);
		out.append(",\n");
		B.toString(out, depth + 1).append("\n");
		return out.append(indent).append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof XorTerm)) {
			return false;
		}
		final XorTerm castB = (XorTerm) b;
		return (A.equals(castB.A) && B.equals(castB.B)) || (A.equals(castB.B) && B.equals(castB.A));
	}

	@Override
	public int hashCode() {
		final int result = 101 * 31 + A.hashCode();
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
	 * new XorTerm(mA, mB); }
	 */

	@Override
	public Boolean evaluate(final ProgramState state) {
		return A.evaluate(state) ^ B.evaluate(state);
	}
}