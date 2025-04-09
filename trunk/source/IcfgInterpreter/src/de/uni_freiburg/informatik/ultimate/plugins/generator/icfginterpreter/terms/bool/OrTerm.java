package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

/**
 * Represents the n-ary boolean function "A or B or C or ..."
 */
public class OrTerm extends BooleanTerm {
	private final BooleanTerm[] mSubTerms;

	public OrTerm(final BooleanTerm... subterms) {
		super(SMTLIBConstants.OR);
		mSubTerms = subterms;
		assert mSubTerms.length >= 1;
	}

	/**
	 * Returns the negated sub-terms inside an {@link AndTerm} <br>
	 * not(or(A, B, ...)) => and(not(A), not(B), ...)
	 */
	@Override
	public BooleanTerm negate() {
		final BooleanTerm[] negatedTerms = new BooleanTerm[mSubTerms.length];

		for (int i = 0; i < mSubTerms.length; i++) {
			negatedTerms[i] = mSubTerms[i].negate();
		}

		return new AndTerm(negatedTerms);
	}

	/**
	 * Returns new {@link OrTerm} after simplifying all sub terms. <br>
	 * If only one sub-term exists, it instead returns that term. <br>
	 * Any sub-terms that are also or-terms are absorbed into the main or-term.
	 */
	@Override
	public BooleanTerm simplify() {
		// Use HashSet to avoid duplicate terms, linked to preserve order (cosmetic decision)
		final LinkedHashSet<BooleanTerm> tempTerms = new LinkedHashSet<>();

		final ArrayList<BooleanTerm> newSubterms = new ArrayList<>(Arrays.asList(mSubTerms));

		while (newSubterms.size() > 0) {
			final BooleanTerm subterm = newSubterms.remove(0).simplify();

			if (subterm instanceof OrTerm) {
				newSubterms.addAll(Arrays.asList(((OrTerm) subterm).mSubTerms));
			} else if (subterm instanceof TrueTerm) {
				return new TrueTerm();
			} else if (subterm instanceof FalseTerm) {
				continue;
			} else {
				tempTerms.add(subterm);
			}
		}

		if (tempTerms.size() == 1) {
			return tempTerms.iterator().next();
		}
		if (tempTerms.size() == 0) {
			return new FalseTerm();
		}

		for (final BooleanTerm tempTerm : tempTerms) {
			if (tempTerms.contains(tempTerm.negate().simplify())) {
				return new TrueTerm();
			}
		}

		// Sort the entries by hash code. Allowed due to commutativity.
		final ArrayList<BooleanTerm> listTerms = new ArrayList<>(tempTerms);
		listTerms.sort((final BooleanTerm x, final BooleanTerm y) -> Util.compareBaseOrder(x, y));

		return new OrTerm(listTerms.toArray(new BooleanTerm[listTerms.size()]));
	}

	@Override
	public ArrayList<BooleanTerm> getSubTerms() {
		return new ArrayList<>(Arrays.asList(mSubTerms));
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		final String indent = Util.getIndent(depth);
		out.append(indent).append("or(\n");

		for (final BooleanTerm subTerm : mSubTerms) {
			subTerm.toString(out, depth + 1);
			out.append(",\n");
		}
		out.append(indent).append(")");

		return out;
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof OrTerm)) {
			return false;
		}
		final OrTerm castB = (OrTerm) b;
		if (mSubTerms.length != castB.mSubTerms.length) {
			return false;
		}
		final HashSet<BooleanTerm> subTermsA = new HashSet<>(Arrays.asList(mSubTerms));
		final HashSet<BooleanTerm> subTermsB = new HashSet<>(Arrays.asList(castB.mSubTerms));

		return subTermsA.containsAll(subTermsB) && subTermsB.containsAll(subTermsA);
	}

	@Override
	public int hashCode() {
		int result = 17;
		for (final BooleanTerm term : mSubTerms) {
			result = result * 31 + term.hashCode();
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
	public Boolean evaluate(final ProgramState currentState, final ProgramState nextState) {
		for (final BooleanTerm subTerm : mSubTerms) {
			if (subTerm.evaluate(currentState, nextState)) {
				return true;
			}
		}

		return false;
	}

	@Override
	public Term toSMTTerm(final Theory theory) {
		if (mSubTerms.length == 1) {
			return mSubTerms[0].toSMTTerm(theory);
		}

		Term A = mSubTerms[0].toSMTTerm(theory);
		for (int i = 1; i < mSubTerms.length; i++) {
			final Term B = mSubTerms[i].toSMTTerm(theory);
			A = Util.makeTerm(mSymbol, theory, A, B);
		}

		return A;
	}

	@Override
	public String toCode() {
		final ArrayList<String> elements = new ArrayList<>();
		for (final BooleanTerm subTerm : mSubTerms) {
			elements.add(subTerm.toCode());
		}
		if (elements.size() == 1) {
			return elements.get(0);
		}
		return "(" + String.join(" || ", elements) + ")";
	}

	@Override
	protected OrTerm replaceSubterms(final ExecutionTerm old, final ExecutionTerm replacement) {
		final BooleanTerm[] subTerms = new BooleanTerm[mSubTerms.length];

		for (int i = 0; i < mSubTerms.length; i++) {
			subTerms[i] = mSubTerms[i].replaceTerm(old, replacement);
		}

		return new OrTerm(subTerms);
	}
}