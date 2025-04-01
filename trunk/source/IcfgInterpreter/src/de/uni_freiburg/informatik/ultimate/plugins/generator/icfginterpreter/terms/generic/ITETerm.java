package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;

/**
 * Represents the ternary function "if A then B else C"
 */
public class ITETerm<T extends ExecutionTerm> {
	public final BooleanTerm A;
	public final T B;
	public final T C;
	public final static String mSymbol = SMTLIBConstants.ITE;

	public ITETerm(final BooleanTerm mA, final T mB, final T mC) {
		A = mA;
		B = mB;
		C = mC;
		assert B.returnType == C.returnType;
	}

	public interface ITE {
		ITE replaceCondition(BooleanTerm replacement);

		BooleanTerm getCondition();
	}

	public ArrayList<ExecutionTerm> getSubTerms() {
		return Util.toList(A, B, C);
	}

	public StringBuilder toString(final StringBuilder out, final int depth) {
		final String indent = Util.getIndent(depth);
		out.append(indent).append("if(\n");
		A.toString(out, depth + 1);
		out.append(indent).append("\n) then {");
		B.toString(out, depth + 1);
		out.append(indent).append("} else {");
		C.toString(out, depth + 1);
		return out.append(indent).append("}");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof ITETerm)) {
			return false;
		}
		final ITETerm<?> castB = (ITETerm<?>) b;
		return A.equals(castB.A) && B.equals(castB.B) && C.equals(castB.C);
	}

	@Override
	public int hashCode() {
		int result = 61 * 31 + A.hashCode();
		result = result * 31 + B.hashCode();
		return result * 31 + C.hashCode();
	}

	public HashSet<Variable> getVariables() {
		final HashSet<Variable> out = A.getVariables();
		out.addAll(B.getVariables());
		out.addAll(C.getVariables());
		return out;
	}

	public Term toSMTTerm(final Theory theory) {
		return Util.makeTerm(mSymbol, theory, A.toSMTTerm(theory), B.toSMTTerm(theory), C.toSMTTerm(theory));
	}

	/*
	 * @Override public <subT extends Domain<subT>> ITETerm<T, out> replaceSubTerm(ExecutionTerm<subT> current,
	 * ExecutionTerm<subT> replacement) { final BooleanTerm mA = A.equals(current) ? (BooleanTerm) replacement : A;
	 * final out mB = B.equals(current) ? (out) replacement : B; final out mC = C.equals(current) ? (out) replacement :
	 * C; return new ITETerm<>(mA, mB, mC); }
	 */

	public Object evaluate(final ProgramState currentState, final ProgramState nextState) {
		if (A.evaluate(currentState, nextState)) {
			return B.evaluate(currentState, nextState);
		}
		return C.evaluate(currentState, nextState);
	}

	public String toCode() {
		return "(" + A + " ? " + B.toCode() + " : " + C.toCode() + ")";
	}
}