package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials;

import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubtermPropertyChecker;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * This represents a Monomial in the form of
 *
 * <pre>
 * Π x_i^{e_i}
 * </pre>
 *
 * where x_i's are variables and e_i are literals.
 *
 * @author Leonard Fichtner (leonard.fichtner@web.de)
 *
 */
public class Monomial {

	/**
	 * Return value for {@link Monomial#isExclusiveVariable}
	 */
	public enum Occurrence {
		NOT, AS_EXCLUSIVE_VARIABlE, NON_EXCLUSIVE_OR_SUBTERM
	};

	/**
	 * Map from Variables to their exponent. Exponent Zero is forbidden. Roots are not prohibited but we cannot handle
	 * them, yet(?).
	 */
	private final Map<Term, Rational> mVariable2Exponent;

	/**
	 * Sort of this term. E.g, "Int" or "Real".
	 */
	private final Sort mSort;

	/**
	 * Monomial that consists of the single Term t raised to the power of r.
	 */
	public Monomial(final Term t, final Rational r) {
		checkIfTermIsLegalVariable(t);
		mSort = t.getSort();
		mVariable2Exponent = Collections.singletonMap(t, r);
	}

	/**
	 * Monomial that represents the product of Monomials.
	 */
	public Monomial(final Monomial... monomials) {
		mSort = monomials[0].getSort();
		mVariable2Exponent = new HashMap<>();
		for (final Monomial monomial : monomials) {
			for (final Map.Entry<Term, Rational> factor : monomial.getVariable2Exponent().entrySet()) {
				assert factor.getKey().getSort() == mSort : "Sort mismatch: " + factor.getKey().getSort() + " vs. "
						+ mSort;
				assert !(factor.getValue().signum() == -1);
				final Rational exp = mVariable2Exponent.get(factor.getKey());
				if (exp == null) {
					mVariable2Exponent.put(factor.getKey(), factor.getValue());
				} else if (exp.isNegative() || factor.getValue().isNegative()) {
					throw new UnsupportedOperationException("Division is only allowed by constants");
				} else {
					final Rational newExp;
					newExp = exp.add(factor.getValue());
					if (newExp.equals(Rational.ZERO)) {
						mVariable2Exponent.remove(factor.getKey());
					} else {
						mVariable2Exponent.put(factor.getKey(), newExp);
					}
				}
			}
		}
	}

	/**
	 * Check if term is of a type that may be a variable of an Monomial.
	 */
	public void checkIfTermIsLegalVariable(final Term term) {
		if (term instanceof TermVariable || term instanceof ApplicationTerm) {
			// term is ok
		} else {
			throw new IllegalArgumentException("Variable of Monomial has to be TermVariable or ApplicationTerm");
		}
	}

	/**
	 * Find out whether this Term is linear.
	 *
	 * @return
	 */
	public boolean isLinear() {
//		return getVariable2Exponent().entrySet().size() == 1 && getVariable2Exponent().values().contains(Rational.ONE);
		return getSingleVariable() != null;
	}

	/**
	 * @return The variable x if this monomial consists of a single variable whose
	 *         exponent is one, return null otherwise.
	 */
	public Term getSingleVariable() {
		final Iterator<Entry<Term, Rational>> it = getVariable2Exponent().entrySet().iterator();
		if (!it.hasNext()) {
			throw new AssertionError("empty monomial are not supported");
		}
		final Entry<Term, Rational> first = it.next();
		if (!first.getValue().equals(Rational.ONE)) {
			return null;
		}
		if (it.hasNext()) {
			return null;
		}
		return first.getKey();
	}

	/**
	 * @return unmodifiable map where each variable is mapped to its exponent.
	 */
	public Map<Term, Rational> getVariable2Exponent() {
		return Collections.unmodifiableMap(mVariable2Exponent);
	}

	/**
	 * @return true iff var is a variable of this {@link Monomial}. Note that for
	 *         returning true it is especially NOT sufficient if var occurs only as
	 *         a subterm of some variable.
	 */
	public boolean isVariable(final Term var) {
		return getVariable2Exponent().keySet().contains(var);
	}

	/**
	 * Find out if var occurs as a proper subterm of some variable or otherwise as a
	 * variable or does not occur at all.
	 *
	 */
	public Occurrence isExclusiveVariable(final Term var) {
		boolean varOccurred = false;
		for (final Entry<Term, Rational> var2exp : getVariable2Exponent().entrySet()) {
			if (var2exp.getKey().equals(var)) {
				if (varOccurred) {
					throw new AssertionError("var occurs twice");
				} else {
					varOccurred = true;
				}
			} else {
				final boolean subjectOccursAsSubterm = new SubtermPropertyChecker(x -> x == var)
						.isSatisfiedBySomeSubterm(var2exp.getKey());
				if (subjectOccursAsSubterm) {
					return Occurrence.NON_EXCLUSIVE_OR_SUBTERM;
				}
			}
		}
		if (varOccurred) {
			return Occurrence.AS_EXCLUSIVE_VARIABlE;
		} else {
			return Occurrence.NOT;
		}
	}

	public Sort getSort() {
		return mSort;
	}

	/**
	 * Transforms this Monomial into a Term that is supported by the solver.
	 *
	 * @param script
	 *            Script for that this term is constructed.
	 */
	public Term toTerm(final Script script) {
		return timesCoefficientToTerm(script, Rational.ONE);
	}

	/**
	 * Transforms this Monomial times the given coefficient into a Term that is supported by the solver.
	 */
	public Term timesCoefficientToTerm(final Script script, final Rational coeff) {
		Term[] factors;
		int i;
		final int size = sumOfExponents();
		if (coeff.equals(Rational.ONE)) {
			factors = new Term[size];
			i = 0;
		}else {
			factors = new Term[size + 1];
			factors[0] = SmtUtils.rational2Term(script, coeff, mSort);
			i = 1;
		}
		for (final Map.Entry<Term, Rational> entry : mVariable2Exponent.entrySet()) {
			final Term factor = entry.getKey();
			final int exponent = entry.getValue().numerator().intValueExact();
			for (int j = 0; j < exponent; j++) {
				factors[i] = factor;
				++i;
			}
		}
		final Term result = SmtUtils.mul(script, mSort, factors);
		return result;
	}

	private int sumOfExponents() {
		Rational size = Rational.ZERO;
		for (final Rational exp : mVariable2Exponent.values()) {
			assert !exp.equals(Rational.ZERO) : "zero is no legal exponent in AffineTerm";
			assert !(exp.signum() == -1);
			assert exp.isIntegral();
			size = size.add(exp);
		}
		return size.numerator().intValueExact();
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		for (final Map.Entry<Term, Rational> entry : mVariable2Exponent.entrySet()) {
			sb.append(entry.getKey());
			sb.append("^" + (entry.getValue().isNegative() ? "[-" : "[") + entry.getValue().abs() + "]");
		}
		String result = sb.toString();
		if (result.charAt(0) == ' ') {
			result = result.substring(1); // Drop first space
		}
		return result;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (mSort == null ? 0 : mSort.hashCode());
		result = prime * result + (mVariable2Exponent == null ? 0 : mVariable2Exponent.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (!(obj instanceof Monomial)) {
			return false;
		}
		final Monomial other = (Monomial) obj;
		if (mSort == null) {
			if (other.getSort() != null) {
				return false;
			}
		} else if (!mSort.equals(other.getSort())) {
			return false;
		}
		if (mVariable2Exponent == null) {
			if (other.getVariable2Exponent() != null) {
				return false;
			}
		} else if (!mVariable2Exponent.equals(other.getVariable2Exponent())) {
			return false;
		}
		return true;
	}

}
