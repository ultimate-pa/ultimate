package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

/**
 * Represents the n-ary function "X * Y * Z * ..."
 */
public class MultiplicationTerm extends IntegerTerm {
	private final IntegerTerm[] subTerms;

	public MultiplicationTerm(final IntegerTerm... mSubterms) {
		super(SMTLIBConstants.MUL);
		subTerms = mSubterms;
		assert subTerms.length > 1;
		for (final IntegerTerm subTerm : subTerms) {
			assert subTerm.returnType == ReturnType.Int;
		}
	}

	/**
	 * Returns "X * Y * Z ..." with arguments simplified
	 */
	@Override
	public IntegerTerm simplify() {
		final IntegerTerm[] mSubTerms = new IntegerTerm[subTerms.length];

		// ... * -X * -Y * ... is equal to ... * X * Y * ...
		int negatedCount = 0;
		for (int i = 0; i < subTerms.length; i++) {
			IntegerTerm subTerm = subTerms[i];
			if (subTerm instanceof NegationTerm) {
				int stackedMinus = 1;

				while (subTerm instanceof NegationTerm) {
					subTerm = ((NegationTerm) subTerm).getSubTerms().get(0);
					stackedMinus++;
				}
				// After this process, we have innerTerm, which is the first non-Negation child
				// and we have stackedMinus, the amount of negations that were stacked.
				// An even amount cancels out; (-(-X)) = X
				negatedCount += stackedMinus % 2;
			}
			mSubTerms[i] = subTerm;
		}

		for (int i = 0; i < mSubTerms.length; i++) {
			mSubTerms[i] = mSubTerms[i].simplify();
		}

		final List<IntegerTerm> subTermList = Arrays.asList(mSubTerms);
		Collections.sort(subTermList, (final IntegerTerm x, final IntegerTerm y) -> Util.compareBaseOrder(x, y));

		// Now, all arguments in mSubTerms are not negation terms.
		// If negatedCount is odd, then the first argument becomes negative.
		if (negatedCount % 2 == 1) {
			subTermList.set(0, subTermList.get(0).negate().simplify());
		}

		return new MultiplicationTerm(subTermList.toArray(new IntegerTerm[subTermList.size()]));
	}

	/**
	 * Returns "-X * Y * Z ..."
	 */
	@Override
	public IntegerTerm negate() {
		final IntegerTerm[] mSubTerms = subTerms.clone();
		mSubTerms[0] = new NegationTerm(mSubTerms[0]);
		return new MultiplicationTerm(mSubTerms);
	}

	@Override
	public ArrayList<IntegerTerm> getSubTerms() {
		return new ArrayList<>(Arrays.asList(subTerms));
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		out.append(Util.getIndent(depth)).append("(");

		subTerms[0].toString(out, 0);
		for (int i = 1; i < subTerms.length; i++) {
			out.append(" * ");
			subTerms[i].toString(out, 0);
		}
		return out.append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof MultiplicationTerm)) {
			return false;
		}
		final MultiplicationTerm castB = (MultiplicationTerm) b;

		final HashSet<IntegerTerm> subTermsA = new HashSet<>(Arrays.asList(subTerms));
		final HashSet<IntegerTerm> subTermsB = new HashSet<>(Arrays.asList(castB.subTerms));

		return subTermsA.containsAll(subTermsB) && subTermsB.containsAll(subTermsA);
	}

	@Override
	public int hashCode() {
		int result = 71;
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
	public Term toSMTTerm(final Theory theory) {
		final Term[] parameters = new Term[subTerms.length];
		for (int i = 0; i < subTerms.length; i++) {
			parameters[i] = subTerms[i].toSMTTerm(theory);
		}
		return Util.makeTerm(mSymbol, theory, parameters);
	}

	/*
	 * @Override public <subT extends Domain<subT>> ExecutionTerm<IntegerDomain> replaceSubTerm(final
	 * ExecutionTerm<subT> current, final ExecutionTerm<subT> replacement) { final IntegerTerm[] mSubTerms = new
	 * IntegerTerm[subTerms.length]; for (int i = 0; i < subTerms.length; i++) { mSubTerms[i] =
	 * subTerms[i].equals(current) ? (IntegerTerm) replacement : subTerms[i]; }
	 *
	 * return new MultiplicationTerm(mSubTerms); }
	 */

	@Override
	public Integer evaluate(final ProgramState state) {
		int out = 1;

		for (final IntegerTerm subTerm : subTerms) {
			out *= subTerm.evaluate(state);
		}

		return out;
	}
}