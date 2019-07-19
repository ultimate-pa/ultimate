package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;

/**
 * This represents a Monomial in the form of
 * 
 * <pre>
 * Π x_i^{e_i}
 * </pre>
 * 
 * where x_i's are variables and e_i are literals.
 * 
 * @author Leonard Fichtner
 *
 */
public class Monomial extends Term {

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
		super(0);
		checkIfTermIsLegalVariable(t);
		mSort = t.getSort();
		mVariable2Exponent = Collections.singletonMap(t, r);
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
	 * Monomial that represents the product of Monomials.
	 */
	public Monomial(final Monomial... monomials) {
		super(0);
		mSort = monomials[0].getSort();
		mVariable2Exponent = new HashMap<>();
		for (final Monomial monomial : monomials) {
			for (final Map.Entry<Term, Rational> factor : monomial.getVariable2Exponent().entrySet()) {
				assert factor.getKey().getSort() == mSort : "Sort mismatch: " + factor.getKey().getSort() + " vs. "
						+ mSort;
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
	 * Monomial that represents the inverse Monomial in the sense of Product (i.e. 1/Monomial)
	 */
	public Monomial(final Monomial monomial) {
		super(0);
		mSort = monomial.getSort();
		if (monomial.getVariable2Exponent().size() == 1) {
			final Term variable = monomial.getVariable2Exponent().keySet().iterator().next();
			final Rational exponent = monomial.getVariable2Exponent().values().iterator().next().negate();
			mVariable2Exponent = Collections.singletonMap(variable, exponent);
			return;
		}

		mVariable2Exponent = new HashMap<>();
		for (final Map.Entry<Term, Rational> variabletoexponent : monomial.getVariable2Exponent().entrySet()) {
			mVariable2Exponent.put(variabletoexponent.getKey(), variabletoexponent.getValue().negate());
		}
	}

	/**
	 * Find out whether this Term is linear.
	 * 
	 * @return
	 */
	public boolean isLinear() {
		return getVariable2Exponent().entrySet().size() == 1 && getVariable2Exponent().values().contains(Rational.ONE);
	}

	/**
	 * @return unmodifiable map where each variable is mapped to its exponent.
	 */
	public Map<Term, Rational> getVariable2Exponent() {
		return Collections.unmodifiableMap(mVariable2Exponent);
	}
	
	/**
	 * @return true iff var is a variable of this {@link Monomial}. Note that for returning true it is especially NOT
	 *         sufficient if var occurs only as a subterm of some variable.
	 */
	public boolean isVariable(final Term var) {
		return getVariable2Exponent().keySet().contains(var);
	}

	@Override
	public Sort getSort() {
		return mSort;
	}

	@Override
	public void toStringHelper(final ArrayDeque<Object> mTodo) {
		throw new UnsupportedOperationException("This is a Monomial. Something went wrong.");
	}

	/**
	 * Transforms this Monomial into a Term that is supported by the solver.
	 *
	 * @param script
	 *            Script for that this term is constructed.
	 */
	public Term toTerm(final Script script) {
		Term[] factors;
		factors = new Term[mVariable2Exponent.size()];
		int i = 0;
		for (final Map.Entry<Term, Rational> entry : mVariable2Exponent.entrySet()) {
			assert !entry.getValue().equals(Rational.ZERO) : "zero is no legal exponent in AffineTerm";
			Term factor = entry.getKey();
			assert entry.getValue().isIntegral();
			// TODO: Ask Matthias about whether it is to be expected that the implementation of isintegral changes.
			// Because then this could be made easier.
			final BigInteger exponent = entry.getValue().numerator().divide(entry.getValue().denominator());
			if (exponent.signum() == 1) {
				final Term singlefactor = factor;
				// Here we could use intValueExact. But I think it would be veeeeery unusual to have such big exponents.
				// Nonetheless: TODO: Better ask Matthias about this
				for (int j = 1; j < exponent.intValue(); j++) {
					factor = SmtUtils.mul(script, mSort, factor, singlefactor);
				}
				factors[i] = factor;
				++i;
			} else {
				final Term singlefactor = factor;
				for (int j = 1; j < exponent.negate().intValue(); j++) {
					factor = SmtUtils.mul(script, mSort, factor, singlefactor);
				}
				// TODO: Ask Matthias whether it is ok, that I multiply with 1/factor instead of directly dividing.
				factors[i] = script.term("/", Rational.ONE.toTerm(mSort), factor);
				++i;
			}
		}
		final Term result = SmtUtils.mul(script, mSort, factors);
		return result;
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
