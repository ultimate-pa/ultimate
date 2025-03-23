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
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

/**
 * Represents the binary function "A != B"
 */
public class DistinctTerm extends BooleanTerm {
	private final ExecutionTerm mA;
	private final ExecutionTerm mB;

	public DistinctTerm(final ExecutionTerm A, final ExecutionTerm B) {
		super(SMTLIBConstants.DISTINCT);
		assert A.returnType.equals(B.returnType);
		mA = A;
		mB = B;
	}

	/**
	 * Returns != A B C D ... with arguments simplified
	 */
	@Override
	public BooleanTerm simplify() {
		if (mA.equals(mB)) {
			// A == B, they are the same term
			return new FalseTerm();
		}

		if (mA instanceof NotTerm) {
			// not(A) != B, becomes A = B
			return new EqualsTerm(mA.getSubTerms().get(0), mB).simplify();
		}

		if (mB instanceof NotTerm) {
			// A != not(B), becomes A = B
			return new EqualsTerm(mA, mB.getSubTerms().get(0)).simplify();
		}

		if (mA instanceof FalseTerm) {
			// false != B, becomes true = B
			return new EqualsTerm(new TrueTerm(), mB).simplify();
		}

		if (mB instanceof FalseTerm) {
			// A != false, becomes A = true
			return new EqualsTerm(mA, new TrueTerm()).simplify();
		}

		final ExecutionTerm A = mA.simplify();
		final ExecutionTerm B = mB.simplify();
		if (Util.compareBaseOrder(A, B) <= 0) {
			return new DistinctTerm(A, B);
		}
		return new DistinctTerm(B, A);
	}

	/**
	 * Returns "A != B"
	 */
	@Override
	public BooleanTerm negate() {
		return new EqualsTerm(mA, mB);
	}

	@Override
	public ArrayList<ExecutionTerm> getSubTerms() {
		return Util.toList(mA, mB);
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		final String indent = Util.getIndent(depth);
		out.append(indent).append("(!=\n");

		mA.toString(out, depth + 1).append("\n");
		mB.toString(out, depth + 1).append("\n");

		return out.append(indent).append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof DistinctTerm)) {
			return false;
		}
		final DistinctTerm castB = (DistinctTerm) b;

		return (mA.equals(castB.mA) && mB.equals(castB.mB)) || (mA.equals(castB.mB) && mB.equals(castB.mA));
	}

	@Override
	public int hashCode() {
		final int result = 23 * 31 + mA.hashCode();
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
		return new NotTerm(new EqualsTerm(mA, mB)).toSMTTerm(theory);

		// return Util.makeTerm(mSymbol, theory, mA.toSMTTerm(theory), mB.toSMTTerm(theory));
	}

	/*
	 * @Override public <subT extends Domain<subT>> ExecutionTerm<BooleanDomain> replaceSubTerm(ExecutionTerm<subT>
	 * current, ExecutionTerm<subT> replacement) { ArrayList<ExecutionTerm<T>> mSubTerms = new ArrayList<>(); for
	 * (ExecutionTerm<T> subTerm : subTerms) { mSubTerms.add(subTerm.equals(current) ? (ExecutionTerm<T>) replacement :
	 * subTerm); }
	 *
	 * return new DistinctTerm<>(mSubTerms); }
	 */

	@Override
	public Boolean evaluate(final ProgramState currentState, final ProgramState nextState) {
		final Object aValue = mA.evaluate(currentState, nextState);
		final Object bValue = mB.evaluate(currentState, nextState);

		return aValue != bValue;
	}
}