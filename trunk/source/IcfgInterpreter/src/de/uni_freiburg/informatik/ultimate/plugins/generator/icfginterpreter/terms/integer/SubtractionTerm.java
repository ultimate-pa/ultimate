package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer;

import java.util.ArrayList;
import java.util.Arrays;
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
 * Represents the binary function "X - Y"
 */
public class SubtractionTerm extends IntegerTerm {
	private final IntegerTerm[] mSubTerms;

	public SubtractionTerm(final IntegerTerm... subterms) {
		super(SMTLIBConstants.MINUS);
		mSubTerms = subterms;
		assert mSubTerms.length > 1;
		for (final IntegerTerm subTerm : mSubTerms) {
			assert subTerm.returnType == ReturnType.Int;
		}
	}

	/**
	 * Returns "X + -Y + -Z ..." with arguments simplified
	 */
	@Override
	public AdditionTerm simplify() {
		final IntegerTerm[] subTerms = new IntegerTerm[mSubTerms.length];

		subTerms[0] = mSubTerms[0].simplify();
		for (int i = 1; i < mSubTerms.length; i++) {
			subTerms[i] = mSubTerms[i].negate().simplify();
		}

		return new AdditionTerm(subTerms);
	}

	/**
	 * Returns "-X + Y + Z ..."
	 */
	@Override
	public AdditionTerm negate() {
		final IntegerTerm[] subTerms = mSubTerms.clone();
		subTerms[0] = mSubTerms[0].negate();
		return new AdditionTerm(subTerms);
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
			out.append(" - ");
			mSubTerms[i].toString(out, 0);
		}
		return out.append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof SubtractionTerm)) {
			return false;
		}
		final SubtractionTerm castB = (SubtractionTerm) b;

		final HashSet<IntegerTerm> subTermsA = new HashSet<>(Arrays.asList(mSubTerms));
		final HashSet<IntegerTerm> subTermsB = new HashSet<>(Arrays.asList(castB.mSubTerms));

		return subTermsA.containsAll(subTermsB) && subTermsB.containsAll(subTermsA);
	}

	@Override
	public int hashCode() {
		int result = 83;
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
		long out = mSubTerms[0].evaluate(currentState, nextState);

		for (int i = 1; i < mSubTerms.length; i++) {
			out -= mSubTerms[i].evaluate(currentState, nextState);
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
		return "(" + String.join(" - ", elements) + ")";
	}

	@Override
	protected SubtractionTerm replaceSubterms(final ExecutionTerm old, final ExecutionTerm replacement) {
		final IntegerTerm[] subTerms = new IntegerTerm[mSubTerms.length];

		for (int i = 0; i < mSubTerms.length; i++) {
			subTerms[i] = mSubTerms[i].replaceTerm(old, replacement);
		}

		return new SubtractionTerm(subTerms);
	}
}