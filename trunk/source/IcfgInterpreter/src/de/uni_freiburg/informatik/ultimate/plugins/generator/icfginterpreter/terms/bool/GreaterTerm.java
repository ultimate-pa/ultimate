package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

/**
 * Represents the binary function "X > Y > Z ..."
 */
public class GreaterTerm extends BooleanTerm {
	private final IntegerTerm[] subTerms;

	public GreaterTerm(final IntegerTerm... mSubTerms) {
		super(SMTLIBConstants.GT);
		subTerms = mSubTerms;
	}

	/**
	 * Returns "... Z < Y < X" with arguments simplified
	 */
	@Override
	public LessTerm simplify() {
		final IntegerTerm[] mSubTerms = new IntegerTerm[subTerms.length];

		final int reverseIndex = subTerms.length - 1;
		for (int i = 0; i < subTerms.length; i++) {
			mSubTerms[reverseIndex - i] = subTerms[i].simplify();
		}

		return new LessTerm(mSubTerms);
	}

	/**
	 * Returns "X <= Y or Y <= Z ..."
	 */
	@Override
	public BooleanTerm negate() {
		if (subTerms.length == 2) {
			return new LessEqualTerm(subTerms[0], subTerms[1]);
		}

		final LessEqualTerm[] pairs = new LessEqualTerm[subTerms.length - 1];

		for (int i = 0; i < subTerms.length - 1; i++) {
			pairs[i] = new LessEqualTerm(subTerms[i], subTerms[i + 1]);
		}

		return new OrTerm(pairs);
	}

	@Override
	public ArrayList<IntegerTerm> getSubTerms() {
		return Util.toList(subTerms);
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		out.append(Util.getIndent(depth)).append("(");

		subTerms[0].toString(out, 0);
		for (int i = 1; i < subTerms.length; i++) {
			out.append(" > ");
			subTerms[i].toString(out, 0);
		}

		return out.append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof GreaterTerm)) {
			return false;
		}
		final LessTerm castB = ((GreaterTerm) b).simplify();

		final ArrayList<IntegerTerm> subTermsA = simplify().getSubTerms();
		final ArrayList<IntegerTerm> subTermsB = castB.getSubTerms();

		return subTermsA.equals(subTermsB);
	}

	@Override
	public int hashCode() {
		int result = 43;
		for (final IntegerTerm subTerm : subTerms) {
			result = result * 31 + subTerm.hashCode();
		}
		return result;
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		final HashSet<Variable> out = subTerms[0].getVariables();
		for (int i = 1; i < subTerms.length; i++) {
			out.addAll(subTerms[i].getVariables());
		}
		return out;
	}

	@Override
	public Term toSMTTerm() {
		final Term[] parameters = new Term[subTerms.length];
		for (int i = 0; i < subTerms.length; i++) {
			parameters[i] = subTerms[i].toSMTTerm();
		}
		return Util.makeTerm(mSymbol, parameters);
	}

	/*
	 * @Override public <subT extends Domain<subT>> ExecutionTerm<BooleanDomain> replaceSubTerm(ExecutionTerm<subT>
	 * current, ExecutionTerm<subT> replacement) { IntegerTerm[] mSubTerms = new IntegerTerm[subTerms.length]; for(int i
	 * = 0; i < subTerms.length; i++) { mSubTerms[i] = subTerms[i].equals(current) ? (IntegerTerm) replacement :
	 * subTerms[i]; }
	 *
	 * return new GreaterTerm(mSubTerms); }
	 */

	@Override
	public Boolean evaluate(final ProgramState state) {
		Integer evaluatedA = subTerms[0].evaluate(state);
		Integer evaluatedB;

		for (int i = 1; i < subTerms.length; i++) {
			evaluatedB = subTerms[i].evaluate(state);
			if (evaluatedA <= evaluatedB) {
				return false;
			}
			evaluatedA = evaluatedB;
		}

		return true;
	}
}