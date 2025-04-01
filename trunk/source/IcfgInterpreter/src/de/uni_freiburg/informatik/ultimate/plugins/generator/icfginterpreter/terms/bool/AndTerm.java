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
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

/**
 * Represents the n-ary boolean function "A and B and C and ..."
 */
public class AndTerm extends BooleanTerm {
	private final BooleanTerm[] subTerms;

	public AndTerm(final BooleanTerm... mSubterms) {
		super(SMTLIBConstants.AND);
		subTerms = mSubterms;
		assert subTerms.length >= 1;
	}

	/**
	 * Returns the negated sub-terms inside an {@link OrTerm} <br>
	 * not(and(A, B, ...)) => or(not(A), not(B), ...)
	 */
	@Override
	public BooleanTerm negate() {
		final BooleanTerm[] negatedTerms = new BooleanTerm[subTerms.length];

		for (int i = 0; i < subTerms.length; i++) {
			negatedTerms[i] = subTerms[i].negate();
		}

		return new OrTerm(negatedTerms);
	}

	private BooleanTerm distribute() {
		for (int i = 0; i < subTerms.length; i++) {
			final BooleanTerm subterm = subTerms[i];
			if (subterm instanceof OrTerm) {
				final OrTerm orTerm = (OrTerm) subterm;
				final ArrayList<BooleanTerm> orTerms = orTerm.getSubTerms();
				final AndTerm[] andTerms = new AndTerm[orTerms.size()];
				for (int j = 0; j < orTerms.size(); j++) {
					// and(or(a, b, c), x, y, ...) =>
					// or(and(a, x, y), and(b, x, y), and(c, x, y), ...)
					subTerms[i] = orTerms.get(j);
					andTerms[j] = new AndTerm(subTerms.clone());
				}

				return new OrTerm(andTerms).simplify();
			}
		}

		return this;
	}

	/**
	 * Returns new {@link AndTerm} after simplifying all sub terms. <br>
	 * If only one sub-term exists, it instead returns that term. <br>
	 * Any sub-terms that are also and-terms are absorbed into the main and-term.
	 */
	@Override
	public BooleanTerm simplify() {
		// Use HashSet to avoid duplicate terms
		final LinkedHashSet<BooleanTerm> tempTerms = new LinkedHashSet<>();

		final ArrayList<BooleanTerm> newSubterms = new ArrayList<>(Arrays.asList(subTerms));

		while (newSubterms.size() > 0) {
			final BooleanTerm subterm = newSubterms.remove(0).simplify();

			if (subterm instanceof AndTerm) {
				newSubterms.addAll(Arrays.asList(((AndTerm) subterm).subTerms));
			} else if (subterm instanceof FalseTerm) {
				return new FalseTerm();
			} else if (subterm instanceof TrueTerm) {
				continue;
			} else {
				tempTerms.add(subterm);
			}
		}

		if (tempTerms.size() == 1) {
			return tempTerms.iterator().next();
		}
		if (tempTerms.size() == 0) {
			return new TrueTerm();
		}

		for (final BooleanTerm tempTerm : tempTerms) {
			if (tempTerms.contains(tempTerm.negate().simplify())) {
				return new FalseTerm();
			}
		}

		// Sort the entries by hash code. Allowed due to commutativity.
		final ArrayList<BooleanTerm> listTerms = new ArrayList<>(tempTerms);
		listTerms.sort((final BooleanTerm x, final BooleanTerm y) -> Util.compareBaseOrder(x, y));

		return new AndTerm(listTerms.toArray(new BooleanTerm[listTerms.size()])).distribute();
	}

	@Override
	public ArrayList<BooleanTerm> getSubTerms() {
		return new ArrayList<>(Arrays.asList(subTerms));
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		final String indent = Util.getIndent(depth);
		out.append(indent).append("and(\n");

		for (final BooleanTerm subTerm : subTerms) {
			subTerm.toString(out, depth + 1);
			out.append(",\n");
		}
		out.append(indent).append(")");

		return out;
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof AndTerm)) {
			return false;
		}
		final AndTerm castB = (AndTerm) b;
		if (subTerms.length != castB.subTerms.length) {
			return false;
		}
		final HashSet<BooleanTerm> subTermsA = new HashSet<>(Arrays.asList(subTerms));
		final HashSet<BooleanTerm> subTermsB = new HashSet<>(Arrays.asList(castB.subTerms));

		return subTermsA.containsAll(subTermsB) && subTermsB.containsAll(subTermsA);
	}

	@Override
	public int hashCode() {
		int result = 13;
		for (final BooleanTerm term : subTerms) {
			result = result * 31 + term.hashCode();
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
	public Boolean evaluate(final ProgramState currentState, final ProgramState nextState) {
		for (final BooleanTerm subTerm : subTerms) {
			if (!subTerm.evaluate(currentState, nextState)) {
				return false;
			}
		}

		return true;
	}

	@Override
	public Term toSMTTerm(final Theory theory) {
		if (subTerms.length == 1) {
			return subTerms[0].toSMTTerm(theory);
		}

		Term A = subTerms[0].toSMTTerm(theory);
		for (int i = 1; i < subTerms.length; i++) {
			final Term B = subTerms[i].toSMTTerm(theory);
			A = Util.makeTerm(mSymbol, theory, A, B);
		}

		return A;
	}

	@Override
	public String toCode() {
		final ArrayList<String> elements = new ArrayList<>();
		for (final BooleanTerm subTerm : subTerms) {
			elements.add(subTerm.toCode());
		}
		if (elements.size() == 1) {
			return elements.get(0);
		}
		return "(" + String.join(" && ", elements) + ")";
	}
}