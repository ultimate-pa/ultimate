package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

/**
 * Represents the n-ary boolean function "A or B or C or ..."
 */
public class OrTerm extends BooleanTerm {
	private final BooleanTerm[] subTerms;

	public OrTerm(final BooleanTerm... mSubterms) {
		super(SMTLIBConstants.OR);
		subTerms = mSubterms;
		assert subTerms.length >= 1;
	}

	/**
	 * Returns the negated sub-terms inside an {@link AndTerm} <br>
	 * not(or(A, B, ...)) => and(not(A), not(B), ...)
	 */
	@Override
	public BooleanTerm negate() {
		final BooleanTerm[] negatedTerms = new BooleanTerm[subTerms.length];

		for (int i = 0; i < subTerms.length; i++) {
			negatedTerms[i] = subTerms[i].negate();
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

		final ArrayList<BooleanTerm> newSubterms = new ArrayList<>(Arrays.asList(subTerms));

		while (newSubterms.size() > 0) {
			final BooleanTerm subterm = newSubterms.remove(0).simplify();

			if (subterm instanceof OrTerm) {
				newSubterms.addAll(Arrays.asList(((OrTerm) subterm).subTerms));
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
		return new ArrayList<>(Arrays.asList(subTerms));
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		final String indent = Util.getIndent(depth);
		out.append(indent).append("or(\n");

		for (final BooleanTerm subTerm : subTerms) {
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
		if (subTerms.length != castB.subTerms.length) {
			return false;
		}
		final HashSet<BooleanTerm> subTermsA = new HashSet<>(Arrays.asList(subTerms));
		final HashSet<BooleanTerm> subTermsB = new HashSet<>(Arrays.asList(castB.subTerms));

		return subTermsA.containsAll(subTermsB) && subTermsB.containsAll(subTermsA);
	}

	@Override
	public int hashCode() {
		int result = 17;
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

	/*
	 * @Override public BooleanDomain evaluate(final HashMap<Variable<?>, Domain<?>> variableDomains) { BooleanDomain
	 * result = subTerms[0].evaluate(variableDomains);
	 *
	 * for (int i = 1; i < subTerms.length; i++) { result = result.or(subTerms[i].evaluate(variableDomains)); } return
	 * result; }
	 *
	 * @Override public <subT extends Domain<subT>> ExecutionTerm<BooleanDomain> replaceSubTerm(final
	 * ExecutionTerm<subT> current, final ExecutionTerm<subT> replacement) { final BooleanTerm[] mSubTerms = new
	 * BooleanTerm[subTerms.length]; for (int i = 0; i < subTerms.length; i++) { mSubTerms[i] =
	 * subTerms[i].equals(current) ? (BooleanTerm) replacement : subTerms[i]; }
	 *
	 * return new OrTerm(mSubTerms); }
	 *
	 *
	 */
	@Override
	public Boolean evaluate(final ProgramState state) {
		for (final BooleanTerm subTerm : subTerms) {
			if (subTerm.evaluate(state)) {
				return true;
			}
		}

		return false;
	}

	@Override
	public Term toSMTTerm() {
		final Term[] parameters = new Term[subTerms.length];
		for (int i = 0; i < subTerms.length; i++) {
			parameters[i] = subTerms[i].toSMTTerm();
		}
		return Util.makeTerm(mSymbol, parameters);
	}
}