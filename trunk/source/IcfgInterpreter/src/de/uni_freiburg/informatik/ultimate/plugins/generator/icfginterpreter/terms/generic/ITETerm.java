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
	public final BooleanTerm mCondition;
	public final T mB;
	public final T mC;
	public final static String mSymbol = SMTLIBConstants.ITE;

	public ITETerm(final BooleanTerm A, final T B, final T C) {
		mCondition = A;
		mB = B;
		mC = C;
		assert mB.returnType == mC.returnType;
	}

	public interface ITE {
		ITE replaceCondition(BooleanTerm replacement);

		BooleanTerm getCondition();
	}

	public ArrayList<ExecutionTerm> getSubTerms() {
		return Util.toList(mCondition, mB, mC);
	}

	public StringBuilder toString(final StringBuilder out, final int depth) {
		final String indent = Util.getIndent(depth);
		out.append(indent).append("if(\n");
		mCondition.toString(out, depth + 1);
		out.append(indent).append("\n) then {");
		mB.toString(out, depth + 1);
		out.append(indent).append("} else {");
		mC.toString(out, depth + 1);
		return out.append(indent).append("}");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof ITETerm)) {
			return false;
		}
		final ITETerm<?> castB = (ITETerm<?>) b;
		return mCondition.equals(castB.mCondition) && mB.equals(castB.mB) && mC.equals(castB.mC);
	}

	@Override
	public int hashCode() {
		int result = 61 * 31 + mCondition.hashCode();
		result = result * 31 + mB.hashCode();
		return result * 31 + mC.hashCode();
	}

	public HashSet<Variable> getVariables() {
		final HashSet<Variable> out = mCondition.getVariables();
		out.addAll(mB.getVariables());
		out.addAll(mC.getVariables());
		return out;
	}

	public Term toSMTTerm(final Theory theory) {
		return Util.makeTerm(mSymbol, theory, mCondition.toSMTTerm(theory), mB.toSMTTerm(theory), mC.toSMTTerm(theory));
	}

	public Object evaluate(final ProgramState currentState, final ProgramState nextState) {
		if (mCondition.evaluate(currentState, nextState)) {
			return mB.evaluate(currentState, nextState);
		}
		return mC.evaluate(currentState, nextState);
	}

	public String toCode() {
		return "(" + mCondition + " ? " + mB.toCode() + " : " + mC.toCode() + ")";
	}
}