package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;

/**
 * 
 * This represents a term in form of
 * 
 * <pre>
 * Σ c_i * x_i^{e_i} + c
 * </pre>
 * 
 * where c_i, c, e_i are literals, and x_i are variables.
 * 
 * @author LeonardFichtner
 *
 */
public class PolynomialTerm extends Term {
    /**
     * Map from Monomials to coefficients. Coefficient Zero is forbidden.
     */
    private final Map<Term, Rational> mMonomial2Coefficient;

    /**
     * Affine constant (coefficient without variable).
     */
    private final Rational mConstant;
    
    /**
	 * Sort of this term. E.g, "Int" or "Real".
	 */
	private final Sort mSort;
	
	/**
	 * PolynomialTerm that represents the Rational r of sort s.
	 */
	public PolynomialTerm(final Sort s, final Rational r) {
		super(0);
		mSort = s;
		mConstant = r;
		mMonomial2Coefficient = Collections.emptyMap();
	}
	
	/**
	 * PolynomialTerm that consists of the single variable tv to the power of one.
	 */
	public PolynomialTerm(final TermVariable tv) {
		super(0);
		mSort = tv.getSort();
		mConstant = Rational.ZERO;
		mMonomial2Coefficient = Collections.singletonMap(new Monomial(tv, Rational.ONE), Rational.ONE);
	}
	
	/**
	 * PolynomialTerm that consists of the single variable tv, to the power of r.
	 */
	public PolynomialTerm(final TermVariable tv, Rational r) {
		super(0);
		mSort = tv.getSort();
		mConstant = Rational.ZERO;
		mMonomial2Coefficient = Collections.singletonMap(new Monomial(tv, r), Rational.ONE);
	}
	
	/**
	 * PolynomialTerm that consists of the single variable which is an application term.
	 * TODO: Find out whether adding an exponent could be of use here?
	 */
	public PolynomialTerm(final ApplicationTerm appTerm) {
		super(0);
		mSort = appTerm.getSort();
		mConstant = Rational.ZERO;
		mMonomial2Coefficient = Collections.singletonMap(new Monomial(appTerm), Rational.ONE);
	}
	
	/**
	 * PolynomialTerm whose variables are given by an array of terms, whose corresponding coefficients are given by the
	 * array coefficients, and whose constant term is given by the Rational constant. All variables are raised to the power of one.
	 */
	public PolynomialTerm(final Sort s, final Term[] terms, final Rational[] coefficients, final Rational constant) {
		super(0);
		mSort = s;
		mConstant = constant;
		if (terms.length != coefficients.length) {
			throw new IllegalArgumentException("number of variables and coefficients different");
		}
		switch (terms.length) {
		case 0:
			mMonomial2Coefficient = Collections.emptyMap();
			break;
		case 1:
			final Term variable = terms[0];
			checkIfTermIsLegalVariable(variable);
			if (coefficients[0].equals(Rational.ZERO)) {
				mMonomial2Coefficient = Collections.emptyMap();
			} else {
				Rational[] rationals = new Rational[1];
				rationals[0] = Rational.ONE;
				mMonomial2Coefficient = Collections.singletonMap(new Monomial(s, terms, rationals), coefficients[0]);
			}
			break;
		default:
			mMonomial2Coefficient = new HashMap<>();
			for (int i = 0; i < terms.length; i++) {
				checkIfTermIsLegalVariable(terms[i]);
				if (!coefficients[i].equals(Rational.ZERO)) {
					mMonomial2Coefficient.put(new Monomial(terms[i], Rational.ONE), coefficients[i]);
				}
			}
			break;
		}
	}
	
	/**
	 * PolynomialTerm whose variables are given by an array of terms, whose corresponding coefficients are given by the
	 * array coefficients, and whose constant term is given by the Rational constant and whose exponents are given by the array exponents.
	 */
	public PolynomialTerm(final Sort s, final Term[] terms, final Rational[] coefficients, final Rational[] exponents, final Rational constant) {
		super(0);
		mSort = s;
		mConstant = constant;
		if (terms.length != coefficients.length || coefficients.length != exponents.length) {
			throw new IllegalArgumentException("number of variables and coefficients different");
		}
		switch (terms.length) {
		case 0:
			mMonomial2Coefficient = Collections.emptyMap();
			break;
		case 1:
			final Term variable = terms[0];
			checkIfTermIsLegalVariable(variable);
			if (coefficients[0].equals(Rational.ZERO)) {
				mMonomial2Coefficient = Collections.emptyMap();
			} else {
				mMonomial2Coefficient = Collections.singletonMap(new Monomial(s, terms, exponents), coefficients[0]);
			}
			break;
		default:
			mMonomial2Coefficient = new HashMap<>();
			for (int i = 0; i < terms.length; i++) {
				checkIfTermIsLegalVariable(terms[i]);
				if (!coefficients[i].equals(Rational.ZERO)) {
					mMonomial2Coefficient.put(new Monomial(terms[i], exponents[i]), coefficients[i]);
				}
			}
			break;
		}
	}
	
	/**
	 * Check if term is of a type that may be a variable of an PolynomialTerm.
	 */
	public void checkIfTermIsLegalVariable(final Term term) {
		if (term instanceof TermVariable || term instanceof ApplicationTerm) {
			// term is ok
		} else {
			throw new IllegalArgumentException("Variable of AffineTerm has to be TermVariable or ApplicationTerm");
		}
	}
	
	/**
	 * Calculate the Map of a sum of given PolynomialTerms.
	 */
	private Map<Term, Rational> CalculateSumMap(final PolynomialTerm... polynomialTerms){
		Map<Term, Rational> map = new HashMap<>();
		for (final PolynomialTerm polynomialTerm : polynomialTerms) {
			for (final Map.Entry<Term, Rational> summand : polynomialTerm.mMonomial2Coefficient.entrySet()) {
				assert summand.getKey().getSort() == mSort : "Sort mismatch: " + summand.getKey().getSort() + " vs. "
						+ mSort;
				final Rational coeff = map.get(summand.getKey());
				if (coeff == null) {
					map.put(summand.getKey(), summand.getValue());
				} else {
					final Rational newCoeff;
					if (SmtSortUtils.isBitvecSort(mSort)) {
						newCoeff = bringValueInRange(coeff.add(summand.getValue()), mSort);
					} else {
						newCoeff = coeff.add(summand.getValue());
					}
					if (newCoeff.equals(Rational.ZERO)) {
						map.remove(summand.getKey());
					} else {
						map.put(summand.getKey(), newCoeff);
					}
				}
			}
		}
		return map;
	}
	
	/**
	 * Calculate the Constant of a sum of given PolynomialTerms.
	 */
	private Rational CalculateSumConstant(final PolynomialTerm...polynomialTerms) {
		Rational constant = Rational.ZERO;
		for (PolynomialTerm polynomialTerm : polynomialTerms) {
			if (SmtSortUtils.isBitvecSort(mSort)) {
				constant = bringValueInRange(constant.add(polynomialTerm.mConstant), mSort);
			} else {
				constant = constant.add(polynomialTerm.mConstant);
			}
		}
		return constant;
	}
	
	//TODO: Make multiplication available for more terms than two
	/**
	 * Polynomial Term that represents the product of exactly two PolynomialTerms.
	 */
	private PolynomialTerm(final PolynomialTerm poly1, final PolynomialTerm poly2) {
		super(0);
		mSort = poly1.getSort();
		mMonomial2Coefficient = new HashMap<>();
		assert poly1.getSort() == poly2.getSort();
		//Multiply Monomials of the two polynomialTerms
		for (final Map.Entry<Term, Rational> summand1 : poly1.mMonomial2Coefficient.entrySet()) {
			for (final Map.Entry<Term, Rational> summand2 : poly2.mMonomial2Coefficient.entrySet()) {
				final Monomial mono = new Monomial((Monomial) summand1.getKey(),(Monomial) summand2.getKey());
				final Rational newCoeff;
				final Rational coeff = mMonomial2Coefficient.get(mono);
				if (coeff == null) {
					newCoeff = summand1.getValue().mul(summand2.getValue());
					mMonomial2Coefficient.put(mono, newCoeff);
				}else {
					//TODO: Probably something with bitvectors should be here, too
					newCoeff = summand1.getValue().mul(summand2.getValue()).add(coeff);
					if (newCoeff.equals(Rational.ZERO)) {
						mMonomial2Coefficient.remove(mono);
					}else {
						mMonomial2Coefficient.put(mono, newCoeff);
					}
				}
			}
		}
		//Multiply Monomials of polynomialTerm 1 with the constant of polynomialTerm 2
		for (final Map.Entry<Term, Rational> summand : poly1.mMonomial2Coefficient.entrySet()) {
			final Rational coeff = mMonomial2Coefficient.get(summand.getKey());
			if (coeff == null) {
				mMonomial2Coefficient.put(summand.getKey(), summand.getValue().mul(poly2.mConstant));
			}else {
				final Rational newCoeff;
				//TODO: Probably something with bitvectors should be here, too
				newCoeff = summand.getValue().mul(poly2.mConstant).add(coeff);
				if (!newCoeff.equals(Rational.ZERO)) {
					mMonomial2Coefficient.put(summand.getKey(), newCoeff);
				}
			}
		}
		//Multiply Monomials of polynomialTerm 2 with the constant of polynomialTerm 1
		for (final Map.Entry<Term, Rational> summand : poly2.mMonomial2Coefficient.entrySet()) {
			final Rational coeff = mMonomial2Coefficient.get(summand.getKey());
			if (coeff == null) {
				mMonomial2Coefficient.put(summand.getKey(), summand.getValue().mul(poly1.mConstant));
			}else {
				final Rational newCoeff;
				//TODO: Probably something with bitvectors should be here, too
				newCoeff = summand.getValue().mul(poly1.mConstant).add(coeff);
				if (!newCoeff.equals(Rational.ZERO)) {
					mMonomial2Coefficient.put(summand.getKey(), newCoeff);
				}
			}
		}
		mConstant = poly1.mConstant.mul(poly2.mConstant);
	}
	
	/**
	 * Calculate the Map of a product of given PolynomialTerms.
	 */
	private PolynomialTerm CalculateProduct(PolynomialTerm... polynomialTerms) {
		PolynomialTerm poly = new PolynomialTerm(polynomialTerms[0], polynomialTerms[1]);
		for (int i = 2; i < polynomialTerms.length; i++) {
			poly = new PolynomialTerm(poly, polynomialTerms[i]);
		}
		return poly;
	}
	
	/**
	 * PolynomialTerm that represents either the sum or the product of polynomialTerms. What function
	 * is to be applied is specified by the "fun" argument.
	 */
	public PolynomialTerm(String functionSymbol, PolynomialTerm... polynomialTerms) {
		super(0);
		mSort = polynomialTerms[0].getSort();
		if (functionSymbol.equals("+")) {
			mMonomial2Coefficient = CalculateSumMap(polynomialTerms);
			mConstant = CalculateSumConstant(polynomialTerms);
		}else if (functionSymbol.equals("*")) {
			//This may look weird but I think its the best option right now.
			PolynomialTerm clone = CalculateProduct(polynomialTerms);
			mMonomial2Coefficient = clone.mMonomial2Coefficient;
			mConstant = clone.mConstant;
		}else {
			throw new IllegalArgumentException("FunctionSymbol must either be a + or a *");
		}
	}
	
	/**
	 * PolynomialTerm that represents the product of polynomialTerm and multiplier.
	 */
	public PolynomialTerm(final PolynomialTerm polynomialTerm, final Rational multiplier) {
		super(0);
		if (multiplier.equals(Rational.ZERO)) {
			mSort = polynomialTerm.getSort();
			mConstant = Rational.ZERO;
			mMonomial2Coefficient = Collections.emptyMap();
		} else {
			mMonomial2Coefficient = new HashMap<>();
			mSort = polynomialTerm.getSort();
			if (SmtSortUtils.isBitvecSort(mSort)) {
				mConstant = bringValueInRange(polynomialTerm.mConstant.mul(multiplier), mSort);
			} else {
				assert mSort.isNumericSort();
				mConstant = polynomialTerm.mConstant.mul(multiplier);
			}
			for (final Map.Entry<Term, Rational> summand : polynomialTerm.mMonomial2Coefficient.entrySet()) {
				mMonomial2Coefficient.put(summand.getKey(), summand.getValue().mul(multiplier));
			}
		}
	}
	
	//TODO: Find out whether the error constructor is necessary -- Indeed it is, handle this when writing the transformer.
	//TODO: Find out how to realize toTerm.
	//TODO: Flatten ApplicationTerms
	
	/**
	 * Use modulo operation to bring Rational in the range of representable values.
	 *
	 * @param bv
	 *            Rational that represents a bitvector
	 * @param sort
	 *            bitvector sort
	 * @return bv % 2^sort.getIndices[0]
	 */
	private static Rational bringValueInRange(final Rational bv, final Sort sort) {
		assert SmtSortUtils.isBitvecSort(sort);
		assert sort.getIndices().length == 1;
		assert bv.isIntegral();
		final int bitsize = sort.getIndices()[0].intValueExact();
		final BigInteger bvBigInt = bv.numerator();
		final BigInteger numberOfValues = BigInteger.valueOf(2).pow(bitsize);
		final BigInteger resultBigInt = BoogieUtils.euclideanMod(bvBigInt, numberOfValues);
		return Rational.valueOf(resultBigInt, BigInteger.ONE);
	}
	
	/**
	 * @return unmodifiable map where each variable is mapped to its coefficient.
	 */
	public Map<Term, Rational> getMonomial2Coefficient() {
		return Collections.unmodifiableMap(mMonomial2Coefficient);
	}
	
	/**
	 * @return whether this polynomial term is just a constant
	 */
	public boolean isConstant() {
		return mMonomial2Coefficient.isEmpty();
	}

	/**
	 * @return whether this polynomial term is zero
	 */
	public boolean isZero() {
		return mConstant.equals(Rational.ZERO) && mMonomial2Coefficient.isEmpty();
	}

	/**
	 * @return the constant summand of this polynomial term
	 */
	public Rational getConstant() {
		return mConstant;
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		for (final Map.Entry<Term, Rational> entry : mMonomial2Coefficient.entrySet()) {
			sb.append(entry.getValue().isNegative() ? " - " : " + ");
			sb.append(entry.getValue().abs() + "*" + entry.getKey());
		}
		if (!mConstant.equals(Rational.ZERO) || sb.length() == 0) {
			if (mConstant.isNegative() || sb.length() > 0) {
				sb.append(mConstant.isNegative() ? " - " : " + ");
			}
			sb.append(mConstant.abs());
		}
		String result = sb.toString();
		if (result.charAt(0) == ' ') {
			result = result.substring(1); // Drop first space
		}
		return result;
	}

	@Override
	public Sort getSort() {
		return mSort;
	}
	
	@Override
	public void toStringHelper(final ArrayDeque<Object> mTodo) {
		throw new UnsupportedOperationException("This is an auxilliary Term and not supported by the solver");
	}
	
	//TODO: Find out whether it should also applied to the exponents
	public static PolynomialTerm applyModuloToAllCoefficients(final Script script, final PolynomialTerm polynomialTerm,
			final BigInteger divident) {
		assert SmtSortUtils.isIntSort(polynomialTerm.getSort());
		final Map<Term, Rational> map = polynomialTerm.getMonomial2Coefficient();
		final Term[] terms = new Term[map.size()];
		final Rational[] coefficients = new Rational[map.size()];
		int offset = 0;
		for (final Entry<Term, Rational> entry : map.entrySet()) {
			terms[offset] = entry.getKey();
			coefficients[offset] =
					SmtUtils.toRational(BoogieUtils.euclideanMod(SmtUtils.toInt(entry.getValue()), divident));
			offset++;
		}
		final Rational constant =
				SmtUtils.toRational(BoogieUtils.euclideanMod(SmtUtils.toInt(polynomialTerm.getConstant()), divident));
		return new PolynomialTerm(polynomialTerm.getSort(), terms, coefficients, constant);
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (mConstant == null ? 0 : mConstant.hashCode());
		result = prime * result + (mSort == null ? 0 : mSort.hashCode());
		result = prime * result + (mMonomial2Coefficient == null ? 0 : mMonomial2Coefficient.hashCode());
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
		if (!(obj instanceof PolynomialTerm)) {
			return false;
		}
		final PolynomialTerm other = (PolynomialTerm) obj;
		if (mConstant == null) {
			if (other.mConstant != null) {
				return false;
			}
		} else if (!mConstant.equals(other.mConstant)) {
			return false;
		}
		if (mSort == null) {
			if (other.mSort != null) {
				return false;
			}
		} else if (!mSort.equals(other.mSort)) {
			return false;
		}
		if (mMonomial2Coefficient == null) {
			if (other.mMonomial2Coefficient != null) {
				return false;
			}
		} else if (!mMonomial2Coefficient.equals(other.mMonomial2Coefficient)) {
			return false;
		}
		return true;
	}
}