package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.math.BigInteger;


import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
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
	 * Map from Variables to their exponent. Exponent Zero is forbidden. 
	 * Roots are not prohibited but we cannot handle them, yet(?).
	 */
	private final Map<Term, Rational> mVariable2Exponent;
	
	/**
	 * Sort of this term. E.g, "Int" or "Real".
	 */
	private final Sort mSort;
	
	/**
	 * Monomial that consists of the single variable tv, to the exponent r.
	 */
	public Monomial(final TermVariable tv, Rational r) {
		super(0);
		mSort = tv.getSort();
		mVariable2Exponent = Collections.singletonMap((Term) tv, r);
	}

	/**
	 * Monomial that consists of the single Term t raised to the power of r.
	 */
	public Monomial(final Term t, Rational r) {
		super(0);
		checkIfTermIsLegalVariable(t);
		mSort = t.getSort();
		mVariable2Exponent = Collections.singletonMap(t, r);
	}
	
	/**
	 * Monomial that consists of the single variable which is an application term.
	 */
	public Monomial(final ApplicationTerm appTerm) {
		super(0);
		mSort = appTerm.getSort();
		mVariable2Exponent = Collections.singletonMap((Term) appTerm, Rational.ONE);
	}
	
	/**
	 * Monomial whose variables are given by an array of terms, whose corresponding exponents are given by the
	 * array exponents.
	 */
	public Monomial(final Sort s, final Term[] terms, final Rational[] exponents) {
		super(0);
		mSort = s;
		if (terms.length != exponents.length) {
			throw new IllegalArgumentException("number of variables and coefficients different");
		}
		switch (terms.length) {
		case 0:
			mVariable2Exponent = Collections.emptyMap();
			break;
		case 1:
			final Term variable = terms[0];
			checkIfTermIsLegalVariable(variable);
			if (exponents[0].equals(Rational.ZERO)) {
				throw new IllegalArgumentException("exponents mustn't be zero");
			} else {
				mVariable2Exponent = Collections.singletonMap(variable, exponents[0]);
			}
			break;
		default:
			mVariable2Exponent = new HashMap<>();
			for (int i = 0; i < terms.length; i++) {
				checkIfTermIsLegalVariable(terms[i]);
				if (!exponents[i].equals(Rational.ZERO)) {
					mVariable2Exponent.put(terms[i], exponents[i]);
				}else {
					throw new IllegalArgumentException("exponents mustn't be zero");
				}
			}
			break;
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
	 * Monomial that represents the product of Monomials.
	 */
	public Monomial(final Monomial... monomials) {
		super(0);
		mSort = monomials[0].getSort();
		mVariable2Exponent = new HashMap<>();
		for (final Monomial monomial : monomials) {
			for (final Map.Entry<Term, Rational> factor : monomial.mVariable2Exponent.entrySet()) {
				assert factor.getKey().getSort() == mSort : "Sort mismatch: " + factor.getKey().getSort() + " vs. "
						+ mSort;
				final Rational exp = mVariable2Exponent.get(factor.getKey());
				if (exp == null) {
					mVariable2Exponent.put(factor.getKey(), factor.getValue());
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
			Term variable = monomial.getVariable2Exponent().keySet().iterator().next();
			Rational exponent = monomial.getVariable2Exponent().values().iterator().next().negate();
			mVariable2Exponent = Collections.singletonMap(variable, exponent);
			return;
		}else {
			mVariable2Exponent = new HashMap<>();
		}
		for (final Map.Entry<Term, Rational> variabletoexponent : monomial.getVariable2Exponent().entrySet()) {
			mVariable2Exponent.put(variabletoexponent.getKey(), variabletoexponent.getValue().negate());
		}
	}
	
	/**
	 * Find out whether this Term is linear.
	 * @return
	 */
	public boolean isLinear() {
		if (mVariable2Exponent.entrySet().size() == 1 && mVariable2Exponent.values().contains(Rational.ONE)) {
		    return true;
		}
		return false;
	}
	
	/**
	 * @return unmodifiable map where each variable is mapped to its exponent.
	 */
	public Map<Term, Rational> getVariable2Exponent() {
		return Collections.unmodifiableMap(mVariable2Exponent);
	}
	
	@Override
	public Sort getSort() {
		return mSort;
	}
	
	//TODO: Find out whether the error constructor is necessary. So far it doesn't look like it, since
	//an ErrorTerm for the PolynomialTerm is enough.
	//TODO: Find out why toStringHelper is necessary and whether this is ok.
	@Override
	public void toStringHelper(final ArrayDeque<Object> mTodo) {
		throw new UnsupportedOperationException("This is a Monomial and should work.");
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
			BigInteger exponent = entry.getValue().numerator().divide(entry.getValue().denominator());
			//Make sure that the exponent is an integer.
			assert entry.getValue().numerator().gcd(entry.getValue().denominator()) != new BigInteger("1");
			//Here we could use intValueExact. But I think it would be veeeeery unusual to have such big exponents.
			for (int j = 1; j < exponent.intValue() ; j++) {
				factor = SmtUtils.mul(script, mSort, factor, factor);
			}
			factors[i] = factor;
			++i;
		}
		final Term result = SmtUtils.mul(script, mSort, factors);
		return result;
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		for (final Map.Entry<Term, Rational> entry : mVariable2Exponent.entrySet()) {
			sb.append(entry.getKey());
			sb.append("^" + (entry.getValue().isNegative() ? "[-" : "[") + 
			entry.getValue().abs() + "]");
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
