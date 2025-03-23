package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

/**
 * Represents the n-ary function "X + Y + Z + ..."
 */
public class AdditionTerm extends IntegerTerm {
	private final IntegerTerm[] subTerms;

	public AdditionTerm(final IntegerTerm... mSubterms) {
		super(SMTLIBConstants.PLUS);
		subTerms = mSubterms;
		assert subTerms.length > 1;
		for (final IntegerTerm subTerm : subTerms) {
			assert subTerm.returnType == ReturnType.Int;
		}
	}

	/**
	 * Returns "X + Y + Z ..." with arguments simplified
	 */
	@Override
	public AdditionTerm simplify() {
		final ArrayList<IntegerTerm> mSubTerms = new ArrayList<>();
		for (final IntegerTerm subTerm : subTerms) {
			mSubTerms.add(subTerm.simplify());
		}

		Collections.sort(mSubTerms, (final IntegerTerm x, final IntegerTerm y) -> Util.compareBaseOrder(x, y));

		return new AdditionTerm(mSubTerms.toArray(new IntegerTerm[mSubTerms.size()]));
	}

	/**
	 * Returns "-X + -Y + -Z ..."
	 */
	@Override
	public AdditionTerm negate() {
		final IntegerTerm[] mSubTerm = new IntegerTerm[subTerms.length];

		for (int i = 0; i < subTerms.length; i++) {
			mSubTerm[i] = subTerms[i].negate();
		}

		return new AdditionTerm(mSubTerm);
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
			out.append(" + ");
			subTerms[i].toString(out, 0);
		}
		return out.append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof AdditionTerm)) {
			return false;
		}
		final AdditionTerm castB = (AdditionTerm) b;

		final HashSet<IntegerTerm> subTermsA = new HashSet<>(Arrays.asList(subTerms));
		final HashSet<IntegerTerm> subTermsB = new HashSet<>(Arrays.asList(castB.subTerms));

		return subTermsA.containsAll(subTermsB) && subTermsB.containsAll(subTermsA);
	}

	@Override
	public int hashCode() {
		int result = 11;
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
	 * return new AdditionTerm(mSubTerms); }
	 */

	@Override
	public Integer evaluate(final ProgramState currentState, final ProgramState nextState) {
		int out = 0;

		for (final IntegerTerm subTerm : subTerms) {
			out += subTerm.evaluate(currentState, nextState);
		}

		return out;
	}
}