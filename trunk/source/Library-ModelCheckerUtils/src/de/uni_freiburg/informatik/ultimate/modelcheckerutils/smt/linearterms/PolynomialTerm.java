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
 * @author Leonard Fichtner
 *
 */
public class PolynomialTerm extends Term implements IPolynomialTerm {
    /**
     * Map from Monomials or Terms to coefficients. Coefficient Zero is forbidden.
     * Make sure that this is always either of type Map<Term, Rational> (Variable2Coefficient) or of type
     * Map<Monomial, Rational> (Monomial2Coefficient).
     * BREAKING THIS CONVENTION WILL LEAD TO NUMEROUS BUGS!
     */
    private final Map<Monomial, Rational> mMonomial2Coefficient;

    /**
     * Affine constant (coefficient without variable).
     */
    private final Rational mConstant;

    /**
	 * Sort of this term. E.g, "Int" or "Real".
	 */
	private final Sort mSort;


	/**
	 * Constructor to be used of all static methods that construct a polynomialTerm.
	 */
	public PolynomialTerm(final Sort s, Rational constant, Map<Monomial, Rational> map) {
		super(0);
		mSort = s;
		mConstant = constant;
		mMonomial2Coefficient = map;
	}
	
	/**
	 * PolynomialTerm whose variables are given by an array of terms, whose corresponding coefficients are given by the
	 * array coefficients, and whose constant term is given by the Rational constant.
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
				final Rational[] rationals = new Rational[1];
				rationals[0] = Rational.ONE;
				mMonomial2Coefficient = Collections.singletonMap(new Monomial(terms[0], Rational.ONE), coefficients[0]);
			}
			break;
		default:
			final HashMap<Monomial, Rational> mapToBe = new HashMap<>();
			for (int i = 0; i < terms.length; i++) {
				checkIfTermIsLegalVariable(terms[i]);
				if (!coefficients[i].equals(Rational.ZERO)) {
					mapToBe.put(new Monomial(terms[i], Rational.ONE), coefficients[i]);
				}
			}
			mMonomial2Coefficient = mapToBe;
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
			throw new IllegalArgumentException("Variable of PolynomialTerm has to be TermVariable or ApplicationTerm");
		}
	}

	/**
	 * Returns a new PolynomialTerm that represents the Rational r of sort s.
	 */
	public static PolynomialTerm polynomialOfRational(final Sort s, final Rational r) {
		return new PolynomialTerm(s, r, Collections.emptyMap());
	}

	/**
	 * Returns a new PolynomialTerm that represents the product of polynomialTerm and multiplier.
	 */
	public static PolynomialTerm polynomialTimesRational(final IPolynomialTerm polynomialTerm, 
																		 final Rational multiplier) {
		if (multiplier.equals(Rational.ZERO)) {
			return new PolynomialTerm(polynomialTerm.getSort(), Rational.ZERO, Collections.emptyMap());
		} else {
			return new PolynomialTerm(polynomialTerm.getSort(), polynomialTerm.getConstant().mul(multiplier),
									  calculateProductMap(polynomialTerm,
													      polynomialOfRational(polynomialTerm.getSort(), multiplier)));
		}
	}
	
	/**
	 * Returns a new PolynomialTerm that represents the product of two polynomialTerms.
	 */
	public static PolynomialTerm polynomialTimesPolynomial(final IPolynomialTerm poly1, final IPolynomialTerm poly2) {
		return new PolynomialTerm(poly1.getSort(), 
				  				  poly1.getConstant().mul(poly2.getConstant()),
				  				  calculateProductMap(poly1, poly2));
	}

	/**
	 * Returns the sum of given polynomials.
	 */
	public static PolynomialTerm polynomialSum(IPolynomialTerm... polynomialArgs) {
		return new PolynomialTerm(polynomialArgs[0].getSort(),
				  calculateSumConstant(polynomialArgs),
				  calculateSumMap(polynomialArgs));
	}

	/**
	 * Calculate the map of the product of two polynomials (in Monomial2Coefficient form).
	 */
	private static Map<Monomial, Rational> calculateProductMap(final IPolynomialTerm poly1, final IPolynomialTerm poly2){
		final Map<Monomial, Rational> map = new HashMap<>();
		//Multiply Monomials of the two polynomialTerms
		for (final Map.Entry<Monomial, Rational> summand1 : poly1.getMonomial2Coefficient().entrySet()) {
			for (final Map.Entry<Monomial, Rational> summand2 : poly2.getMonomial2Coefficient().entrySet()) {
				final Monomial mono = new Monomial(summand1.getKey(),summand2.getKey());
				final Rational newCoeff;
				final Rational coeff = map.get(mono);
				if (coeff == null) {
					newCoeff = summand1.getValue().mul(summand2.getValue());
					map.put(mono, newCoeff);
				}else {
					//TODO: Probably something with bitvectors should be here, too
					newCoeff = summand1.getValue().mul(summand2.getValue()).add(coeff);
					if (newCoeff.equals(Rational.ZERO)) {
						map.remove(mono);
					}else {
						map.put(mono, newCoeff);
					}
				}
			}
		}

		//Multiply Monomials of polynomialTerm 1 with the constant of polynomialTerm 2
		for (final Map.Entry<Monomial, Rational> summand : poly1.getMonomial2Coefficient().entrySet()) {
			final Rational coeff = map.get(summand.getKey());
			final Rational newCoeff;
			if (coeff == null) {
				newCoeff = summand.getValue().mul(poly2.getConstant());
				if (!newCoeff.equals(Rational.ZERO)) {
					map.put(summand.getKey(), newCoeff);
				}
			}else {
				//TODO: Probably something with bitvectors should be here, too
				newCoeff = summand.getValue().mul(poly2.getConstant()).add(coeff);
				if (!newCoeff.equals(Rational.ZERO)) {
					map.put(summand.getKey(), newCoeff);
				}
			}
		}

		//Multiply Monomials of polynomialTerm 2 with the constant of polynomialTerm 1
		for (final Map.Entry<Monomial, Rational> summand : poly2.getMonomial2Coefficient().entrySet()) {
			final Rational coeff = map.get(summand.getKey());
			final Rational newCoeff;
			if (coeff == null) {
				newCoeff = summand.getValue().mul(poly1.getConstant());
				if (!newCoeff.equals(Rational.ZERO)) {
					map.put(summand.getKey(), newCoeff);
				}
			}else {
				//TODO: Probably something with bitvectors should be here, too
				newCoeff = summand.getValue().mul(poly1.getConstant()).add(coeff);
				if (!newCoeff.equals(Rational.ZERO)) {
					map.put(summand.getKey(), newCoeff);
				}
			}
		}
		return shrinkMap(map);
	}

	/**
	 * Returns a shrinked version of a map if possible. Returns the given map otherwise.
	 */
	private static Map<Monomial, Rational> shrinkMap(Map<Monomial, Rational> map){
		if (map.size() == 0) {
			return Collections.emptyMap();
		}
		else if (map.size() == 1) {
			Entry<Monomial, Rational> entry = map.entrySet().iterator().next();
			return Collections.singletonMap(entry.getKey(), entry.getValue());
		}
		return map;
	}
	
	/**
	 * Calculate the constant of a sum of given IPolynomialTerms.
	 */
	private static Rational calculateSumConstant(final IPolynomialTerm...polynomialTerms) {
		Rational constant = Rational.ZERO;
		Sort s = polynomialTerms[0].getSort();
		for (final IPolynomialTerm polynomialTerm : polynomialTerms) {
			if (SmtSortUtils.isBitvecSort(s)) {
				constant = bringValueInRange(constant.add(polynomialTerm.getConstant()), s);
			} else {
				constant = constant.add(polynomialTerm.getConstant());
			}
		}
		return constant;
	}
	
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
	 * Calculate the map of a sum of given PolynomialTerms (in Monomial2Coefficient form).
	 */
	private static Map<Monomial, Rational> calculateSumMap(final IPolynomialTerm... polynomialTerms){
		final Map<Monomial, Rational> map = new HashMap<>();
		Sort s = polynomialTerms[0].getSort();
		for (final IPolynomialTerm polynomialTerm : polynomialTerms) {
			for (final Map.Entry<Monomial, Rational> summand : polynomialTerm.getMonomial2Coefficient().entrySet()) {
				assert summand.getKey().getSort() == s : "Sort mismatch: " + summand.getKey().getSort() + " vs. "
						+ s;
				final Rational coeff = map.get(summand.getKey());
				if (coeff == null) {
					map.put(summand.getKey(), summand.getValue());
				} else {
					final Rational newCoeff;
					if (SmtSortUtils.isBitvecSort(s)) {
						newCoeff = bringValueInRange(coeff.add(summand.getValue()), s);
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
		return shrinkMap(map);
	}

	/**
	 * Auxiliary polynomial term that represents an error during the translation process, e.g., if original term had wrong sorts.
	 */
	public PolynomialTerm() {
		super(0);
		mMonomial2Coefficient = null;
		mConstant = null;
		mSort = null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.IPolynomialTerm#isErrorTerm()
	 */
	@Override
	public boolean isErrorTerm() {
		if (mMonomial2Coefficient == null) {
			assert mConstant == null;
			assert mSort == null;
			return true;
		} else {
			assert mConstant != null;
			assert mSort != null;
			return false;
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.IPolynomialTerm#toTerm(de.uni_freiburg.informatik.ultimate.logic.Script)
	 */
	@Override
	public Term toTerm(final Script script) {
		Term[] summands;
		if (mConstant.equals(Rational.ZERO)) {
			summands = new Term[getMonomial2Coefficient().size()];
		} else {
			summands = new Term[getMonomial2Coefficient().size() + 1];
		}
		int i = 0;
		for (final Map.Entry<Monomial, Rational> entry : getMonomial2Coefficient().entrySet()) {
			assert !entry.getValue().equals(Rational.ZERO) : "zero is no legal coefficient in PolynomialTerm";
			if (entry.getValue().equals(Rational.ONE)) {
				summands[i] = (entry.getKey()).toTerm(script);
			} else {
				final Term coeff = SmtUtils.rational2Term(script, entry.getValue(), mSort);
				summands[i] = SmtUtils.mul(script, mSort, coeff, (entry.getKey()).toTerm(script));
			}
			++i;
		}
		if (!mConstant.equals(Rational.ZERO)) {
			assert mConstant.isIntegral() || SmtSortUtils.isRealSort(mSort);
			summands[i] = SmtUtils.rational2Term(script, mConstant, mSort);
		}
		final Term result = SmtUtils.sum(script, mSort, summands);
		return result;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.IPolynomialTerm#getMonomial2Coefficient()
	 */
	@Override
	public Map<Monomial, Rational> getMonomial2Coefficient() {
		return mMonomial2Coefficient;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.IPolynomialTerm#getConstant()
	 */
	@Override
	public Rational getConstant() {
		return mConstant;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.IPolynomialTerm#isConstant()
	 */
	@Override
	public boolean isConstant() {
		return getMonomial2Coefficient().isEmpty();
	}

	@Override
	public boolean isAffine() {
		return false;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.IPolynomialTerm#isZero()
	 */
	@Override
	public boolean isZero() {
		return mConstant.equals(Rational.ZERO) && mMonomial2Coefficient.isEmpty();
	}

	/**
	 * Given a Variable2Coefficients-map, this turns it into a Monomial2Coefficients-map.
	 */
	private Map<Monomial, Rational> turnVariableMapIntoMonomialMap(final Map<Term, Rational> termMap){
		switch (termMap.size()) {
		case 0:
			return Collections.emptyMap();
		case 1:
			final Map.Entry<Term, Rational> singleEntry = termMap.entrySet().iterator().next();
			return Collections.singletonMap(new Monomial(singleEntry.getKey(), Rational.ONE), singleEntry.getValue());
		default:
			final Map<Monomial, Rational> MonoMap = new HashMap<>();
			for (final Map.Entry<Term, Rational> entry : termMap.entrySet()) {
				if (entry.getKey() instanceof Monomial) {
					throw new IllegalArgumentException("This map has monomials in it. Something before went wrong!");
				}
				MonoMap.put(new Monomial(entry.getKey(),  Rational.ONE), entry.getValue());
			}
			return MonoMap;
			}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		for (final Map.Entry<Monomial, Rational> entry : getMonomial2Coefficient().entrySet()) {
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

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.IPolynomialTerm#getSort()
	 */
	@Override
	public Sort getSort() {
		return mSort;
	}

	@Override
	public void toStringHelper(final ArrayDeque<Object> mTodo) {
		throw new UnsupportedOperationException("This is an auxilliary Term and not supported by the solver");
	}

	public static IPolynomialTerm applyModuloToAllCoefficients(final Script script, final IPolynomialTerm polynomialTerm,
			final BigInteger divident) {
		assert SmtSortUtils.isIntSort(polynomialTerm.getSort());
		final Map<Monomial, Rational> map = polynomialTerm.getMonomial2Coefficient();
		final Term[] terms = new Term[map.size()];
		final Rational[] coefficients = new Rational[map.size()];
		int offset = 0;
		for (final Entry<Monomial, Rational> entry : map.entrySet()) {
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