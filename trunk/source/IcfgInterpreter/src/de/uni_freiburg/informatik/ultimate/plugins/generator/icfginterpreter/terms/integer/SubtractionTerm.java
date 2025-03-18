package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

/**
 * Represents the binary function "X - Y"
 */
public class SubtractionTerm extends IntegerTerm {
	private final IntegerTerm[] subTerms;

	public SubtractionTerm(final IntegerTerm... mSubterms) {
		super(SMTLIBConstants.MINUS);
		subTerms = mSubterms;
		assert subTerms.length > 1;
		for (final IntegerTerm subTerm : subTerms) {
			assert subTerm.returnType == ReturnType.Int;
		}
	}

	/**
	 * Returns "X + -Y + -Z ..." with arguments simplified
	 */
	@Override
	public AdditionTerm simplify() {
		final IntegerTerm[] mSubTerms = new IntegerTerm[subTerms.length];

		mSubTerms[0] = subTerms[0].simplify();
		for (int i = 1; i < subTerms.length; i++) {
			mSubTerms[i] = subTerms[i].negate().simplify();
		}

		return new AdditionTerm(mSubTerms);
	}

	/**
	 * Returns "-X + Y + Z ..."
	 */
	@Override
	public AdditionTerm negate() {
		final IntegerTerm[] mSubTerms = subTerms.clone();
		mSubTerms[0] = subTerms[0].negate();
		return new AdditionTerm(mSubTerms);
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
			out.append(" - ");
			subTerms[i].toString(out, 0);
		}
		return out.append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof SubtractionTerm)) {
			return false;
		}
		final SubtractionTerm castB = (SubtractionTerm) b;

		final HashSet<IntegerTerm> subTermsA = new HashSet<>(Arrays.asList(subTerms));
		final HashSet<IntegerTerm> subTermsB = new HashSet<>(Arrays.asList(castB.subTerms));

		return subTermsA.containsAll(subTermsB) && subTermsB.containsAll(subTermsA);
	}

	@Override
	public int hashCode() {
		int result = 83;
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
	 * return new SubtractionTerm(mSubTerms); }
	 */

	@Override
	public Integer evaluate(final ProgramState state) {
		int out = subTerms[0].evaluate(state);

		for (int i = 1; i < subTerms.length; i++) {
			out -= subTerms[i].evaluate(state);
		}

		return out;
	}
}