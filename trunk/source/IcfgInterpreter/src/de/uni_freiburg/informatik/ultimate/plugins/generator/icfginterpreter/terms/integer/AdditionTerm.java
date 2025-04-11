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
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ReturnType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

/**
 * Represents the n-ary function "X + Y + Z + ..."
 */
public class AdditionTerm extends IntegerTerm {
	private final IntegerTerm[] mSubTerms;

	public AdditionTerm(final IntegerTerm... subterms) {
		super(SMTLIBConstants.PLUS);
		mSubTerms = subterms;
		assert mSubTerms.length > 1;
		for (final IntegerTerm subTerm : mSubTerms) {
			assert subTerm.returnType == ReturnType.Int;
		}
	}

	/**
	 * Returns "X + Y + Z ..." with arguments simplified
	 */
	@Override
	public AdditionTerm simplify() {
		final ArrayList<IntegerTerm> subTerms = new ArrayList<>();
		for (final IntegerTerm subTerm : mSubTerms) {
			if (subTerm instanceof final AdditionTerm at) {
				// simplify the underlying addition term and flatten it into this term
				subTerms.addAll(at.simplify().getSubTerms());
				continue;
			}
			subTerms.add(subTerm.simplify());
		}

		Collections.sort(subTerms, (final IntegerTerm x, final IntegerTerm y) -> Util.compareBaseOrder(x, y));

		return new AdditionTerm(subTerms.toArray(new IntegerTerm[subTerms.size()]));
	}

	/**
	 * Returns "-X + -Y + -Z ..."
	 */
	@Override
	public AdditionTerm negate() {
		final IntegerTerm[] subTerms = new IntegerTerm[mSubTerms.length];

		for (int i = 0; i < mSubTerms.length; i++) {
			subTerms[i] = mSubTerms[i].negate();
		}

		return new AdditionTerm(mSubTerms);
	}

	@Override
	public ArrayList<IntegerTerm> getSubTerms() {
		return new ArrayList<>(Arrays.asList(mSubTerms));
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		out.append(Util.getIndent(depth)).append("(");

		mSubTerms[0].toString(out, 0);
		for (int i = 1; i < mSubTerms.length; i++) {
			out.append(" + ");
			mSubTerms[i].toString(out, 0);
		}
		return out.append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof AdditionTerm)) {
			return false;
		}
		final AdditionTerm castB = (AdditionTerm) b;

		final HashSet<IntegerTerm> subTermsA = new HashSet<>(Arrays.asList(mSubTerms));
		final HashSet<IntegerTerm> subTermsB = new HashSet<>(Arrays.asList(castB.mSubTerms));

		return subTermsA.containsAll(subTermsB) && subTermsB.containsAll(subTermsA);
	}

	@Override
	public int hashCode() {
		int result = 11;
		for (final IntegerTerm subTerm : mSubTerms) {
			result = result * 31 + subTerm.hashCode();
		}
		return result;
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		final HashSet<Variable> out = mSubTerms[0].getVariables();
		for (int i = 1; i < mSubTerms.length; i++) {
			out.addAll(mSubTerms[i].getVariables());
		}
		return out;
	}

	@Override
	public Term toSMTTerm(final Theory theory) {
		final Term[] parameters = new Term[mSubTerms.length];
		for (int i = 0; i < mSubTerms.length; i++) {
			parameters[i] = mSubTerms[i].toSMTTerm(theory);
		}
		return Util.makeTerm(mSymbol, theory, parameters);
	}

	@Override
	public Long evaluate(final ProgramState currentState, final ProgramState nextState) {
		long out = 0L;

		for (final IntegerTerm subTerm : mSubTerms) {
			out += subTerm.evaluate(currentState, nextState);
		}

		return out;
	}

	@Override
	public String toCode() {
		final ArrayList<String> elements = new ArrayList<>();
		for (final IntegerTerm subTerm : mSubTerms) {
			elements.add(subTerm.toCode());
		}
		if (elements.size() == 1) {
			return elements.get(0);
		}
		return "(" + String.join(" + ", elements) + ")";
	}

	@Override
	protected AdditionTerm replaceSubterms(final ExecutionTerm old, final ExecutionTerm replacement) {
		final IntegerTerm[] subTerms = new IntegerTerm[mSubTerms.length];

		for (int i = 0; i < mSubTerms.length; i++) {
			subTerms[i] = mSubTerms[i].replaceTerm(old, replacement);
		}

		return new AdditionTerm(subTerms);
	}
}