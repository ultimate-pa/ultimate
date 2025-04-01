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
	private final BooleanTerm mA;
	private final BooleanTerm mB;

	public XorTerm(final BooleanTerm A, final BooleanTerm B) {
		super(SMTLIBConstants.XOR);
		mA = A;
		mB = B;
	}

	/**
	 * Returns the logically equivalent "(not(A) and B) or (A and not(B))" after simplifying it.
	 */
	@Override
	public BooleanTerm simplify() {
		final BooleanTerm notAandB = new AndTerm(mA.negate(), mB);

		final BooleanTerm AandnotB = new AndTerm(mA, mB.negate());

		return new OrTerm(notAandB, AandnotB).simplify();
	}

	/**
	 * Returns "(A and B) or (not(A) and not(B))"
	 */
	@Override
	public BooleanTerm negate() {
		final BooleanTerm AandB = new AndTerm(mA, mB);

		final BooleanTerm notAandnotB = new AndTerm(mA.negate(), mB.negate());
		return new OrTerm(AandB, notAandnotB);
	}

	@Override
	public ArrayList<BooleanTerm> getSubTerms() {
		return new ArrayList<>(Arrays.asList(mA, mB));
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		final String indent = Util.getIndent(depth);
		out.append(indent).append("xor(\n");
		mA.toString(out, depth + 1);
		out.append(",\n");
		mB.toString(out, depth + 1).append("\n");
		return out.append(indent).append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof XorTerm)) {
			return false;
		}
		final XorTerm castB = (XorTerm) b;
		return (mA.equals(castB.mA) && mB.equals(castB.mB)) || (mA.equals(castB.mB) && mB.equals(castB.mA));
	}

	@Override
	public int hashCode() {
		final int result = 101 * 31 + mA.hashCode();
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
		return mA.evaluate(currentState, nextState) ^ mB.evaluate(currentState, nextState);
	}

	@Override
	public String toCode() {
		return "(" + mA.toCode() + " ^ " + mB.toCode() + ")";
	}
}