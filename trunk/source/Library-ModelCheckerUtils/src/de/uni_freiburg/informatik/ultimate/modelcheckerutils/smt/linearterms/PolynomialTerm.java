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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ThreadInstance;
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
public class PolynomialTerm extends Term {
    /**
     * Map from Monomials or Terms to coefficients. Coefficient Zero is forbidden.
     * Make sure that this is always either of type Map<Term, Rational> (Variable2Coefficient) or of type
     * Map<Monomial, Rational> (Monomial2Coefficient).
     * BREAKING THIS CONVENTION WILL LEAD TO NUMEROUS BUGS!
     */
    private final Object mTerm2Coefficient;

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
		mTerm2Coefficient = Collections.emptyMap();
	}
	
	/**
	 * PolynomialTerm that represents the product of polynomialTerm and multiplier.
	 */
	public PolynomialTerm(final PolynomialTerm polynomialTerm, final Rational multiplier) {
		super(0);
			mSort = polynomialTerm.getSort();
		if (multiplier.equals(Rational.ZERO)) {
			mConstant = Rational.ZERO;
			mTerm2Coefficient = Collections.emptyMap();
		} else {
			mConstant = polynomialTerm.getConstant().mul(multiplier);
			mTerm2Coefficient = calculateProductMap(polynomialTerm, 
													new PolynomialTerm(polynomialTerm.getSort(), multiplier));
		}
	}

	/**
	 * PolynomialTerm that consists of the single variable tv to the power of one.
	 */
	public PolynomialTerm(final TermVariable tv) {
		super(0);
		mSort = tv.getSort();
		mConstant = Rational.ZERO;
		mTerm2Coefficient = Collections.singletonMap(tv, Rational.ONE);
	}
	
	/**
	 * PolynomialTerm that consists of the single variable tv, with coefficient r.
	 */
	public PolynomialTerm(final TermVariable tv, Rational r) {
		super(0);
		mSort = tv.getSort();
		mConstant = Rational.ZERO;
		mTerm2Coefficient = Collections.singletonMap(tv, r);
	}
	
	/**
	 * PolynomialTerm that consists of the single variable which is an application term.
	 */
	public PolynomialTerm(final ApplicationTerm appTerm) {
		super(0);
		mSort = appTerm.getSort();
		mConstant = Rational.ZERO;
		mTerm2Coefficient = Collections.singletonMap(appTerm, Rational.ONE);
	}
	
	/**
	 * {@link PolynomialTerm} that consists of the single variable that is represented by
	 * the {@link Term} t.
	 */
	public PolynomialTerm(final Term t) {
		super(0);
		mSort = t.getSort();
		mConstant = Rational.ZERO;
		mTerm2Coefficient = Collections.singletonMap(t, Rational.ONE);
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
			mTerm2Coefficient = Collections.emptyMap();
			break;
		case 1:
			final Term variable = terms[0];
			checkIfTermIsLegalVariable(variable);
			if (coefficients[0].equals(Rational.ZERO)) {
				mTerm2Coefficient = Collections.emptyMap();
			} else {
				Rational[] rationals = new Rational[1];
				rationals[0] = Rational.ONE;
				mTerm2Coefficient = Collections.singletonMap(terms[0], coefficients[0]);
			}
			break;
		default:
			HashMap<Term, Rational> mapToBe = new HashMap<>();
			for (int i = 0; i < terms.length; i++) {
				checkIfTermIsLegalVariable(terms[i]);
				if (!coefficients[i].equals(Rational.ZERO)) {
					mapToBe.put(terms[i], coefficients[i]);
				}
			}
			mTerm2Coefficient = mapToBe;
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
	 * Turns a given array of polynomial terms into a new single polynomial term which represents
	 * the addition of the given polynomial terms and returns it.
	 */
	public static PolynomialTerm constructAddition(PolynomialTerm... polynomialTerms) {
	    return new PolynomialTerm(polynomialTerms);
	}

	/**
	 * Constructor for Addition of polynomial terms.
	 */
	private PolynomialTerm(PolynomialTerm... polynomialTerms) {
		super(0);
		mSort = polynomialTerms[0].getSort();
		mTerm2Coefficient = calculateSumMap(polynomialTerms);
		mConstant = calculateSumConstant(polynomialTerms);
	}

	/**
	 * Calculate the map of a sum of given PolynomialTerms.
	 */
	private Object calculateSumMap(final PolynomialTerm... polynomialTerms){
		if (someTermIsPolynomial(polynomialTerms)) {
			return calculateSumMapOfPolynomials(polynomialTerms);
		}
		return calculateSumMapOfAffineTerms(polynomialTerms);
	}
	
	/**
	 * Returns true when one of the given Terms is truly polynomial (not representable
	 * by an AffineTerm)
	 */
	private boolean someTermIsPolynomial(final PolynomialTerm...polynomialTerms) {
		for (final PolynomialTerm polynomialTerm: polynomialTerms) {
			if (!polynomialTerm.isLinear()) {
				return true;
			}
		}
		return false;
	}
	
	/**
	 * Calculate the map of the sum of polynomials in Monomial2Coefficient form.
	 */
	private Map<Monomial, Rational> calculateSumMapOfPolynomials(final PolynomialTerm... polynomialTerms){
		Map<Monomial, Rational> map = new HashMap<>();
		for (final PolynomialTerm polynomialTerm : polynomialTerms) {
			for (final Map.Entry<Monomial, Rational> summand : polynomialTerm.getMonomial2Coefficient().entrySet()) {
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
	 * Calculate the map of the sum of polynomials in Variable2Coefficient form.
	 */
	private Map<Term, Rational> calculateSumMapOfAffineTerms(final PolynomialTerm... polynomialTerms){
		Map<Term, Rational> map = new HashMap<>();
		for (final PolynomialTerm polynomialTerm : polynomialTerms) {
			for (final Map.Entry<Term, Rational> summand : polynomialTerm.getVariable2Coefficient().entrySet()) {
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
		return (Map<Term, Rational>) map;
	}
	
	/**
	 * Calculate the constant of a sum of given PolynomialTerms.
	 */
	private Rational calculateSumConstant(final PolynomialTerm...polynomialTerms) {
		Rational constant = Rational.ZERO;
		for (PolynomialTerm polynomialTerm : polynomialTerms) {
			if (SmtSortUtils.isBitvecSort(mSort)) {
				constant = bringValueInRange(constant.add(polynomialTerm.getConstant()), mSort);
			} else {
				constant = constant.add(polynomialTerm.getConstant());
			}
		}
		return constant;
	}
	
	/**
	 * Turns a given array of polynomial terms into a new single polynomial term which represents
	 * the product of the given polynomial terms and returns it.
	 */
	public static PolynomialTerm constructProduct(PolynomialTerm... polynomialTerms) {
		if (polynomialTerms.length == 1) {
			return polynomialTerms[0];
		}
		PolynomialTerm poly = new PolynomialTerm(polynomialTerms[0], polynomialTerms[1]);
		for (int i = 2; i < polynomialTerms.length; i++) {
			poly = new PolynomialTerm(poly, polynomialTerms[i]);
		}
		return poly;
	}

	/**
	 * Polynomial term that represents the product of exactly two PolynomialTerms.
	 */
	private PolynomialTerm(final PolynomialTerm poly1, final PolynomialTerm poly2) {
		super(0);
		mSort = poly1.getSort();
		mTerm2Coefficient = calculateProductMap(poly1, poly2);
		mConstant = poly1.getConstant().mul(poly2.getConstant());
	}
	
	/**
	 * Calculate the map of the product of two polynomials.
	 */
	private Object calculateProductMap(final PolynomialTerm poly1, final PolynomialTerm poly2) {
		if (!poly1.isLinear() || !poly2.isLinear() || (!poly1.isConstant() && !poly2.isConstant())) {
			return calculateProductMapOfPolynomials(poly1, poly2);
		}
		return calculateProductMapOfAffineTerms(poly1, poly2);
	}
	
	/**
	 * Calculate the map of the product of two polynomials in Monomial2Coefficient form.
	 */
	private Map<Monomial, Rational> calculateProductMapOfPolynomials(final PolynomialTerm poly1, PolynomialTerm poly2){
		Map<Monomial, Rational> map = new HashMap<>();
		//Multiply Monomials of the two polynomialTerms
		for (final Map.Entry<Monomial, Rational> summand1 : poly1.getMonomial2Coefficient().entrySet()) {
			for (final Map.Entry<Monomial, Rational> summand2 : poly2.getMonomial2Coefficient().entrySet()) {
				final Monomial mono = new Monomial((Monomial) summand1.getKey(),(Monomial) summand2.getKey());
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
		return map;
	}
	
	/**
	 * Calculate the map of the product of polynomials in Variable2Coefficient form.
	 */
	private Map<Term, Rational> calculateProductMapOfAffineTerms(PolynomialTerm poly1, PolynomialTerm poly2){
		Map<Term, Rational> map = new HashMap<>();
		if (poly1.isConstant()) {
			if (poly1.getConstant().equals(Rational.ZERO)) {
				return map;
			}
			for (final Map.Entry<Term, Rational> summand : poly2.getVariable2Coefficient().entrySet()) {
				map.put(summand.getKey(), summand.getValue().mul(poly1.getConstant()));
			}
		//poly2 must be a constant then.
		}else {
			if (poly2.getConstant().equals(Rational.ZERO)) {
				return map;
			}
			for (final Map.Entry<Term, Rational> summand : poly1.getVariable2Coefficient().entrySet()) {
				map.put(summand.getKey(), summand.getValue().mul(poly2.getConstant()));
			}
		}
		return map;
	}
	
	/**
	 * Turns a given array of polynomial terms into a new single polynomial term which represents
	 * the division of the given polynomial terms and returns it. At the moment this only supports
	 * division by Constants.
	 */
	public static PolynomialTerm constructDivision(PolynomialTerm...polynomialTerms) {
		if (polynomialTerms.length == 1) {
			return polynomialTerms[0];
		}
		for (int i = 0; i < polynomialTerms.length; i++) {
			if (!polynomialTerms[i].isConstant()) {
				throw new UnsupportedOperationException("Division by Variables not supported!");
			}
		}
		PolynomialTerm poly = new PolynomialTerm(polynomialTerms[0], polynomialTerms[1]);
		for (int i = 2; i < polynomialTerms.length; i++) {
			poly = new PolynomialTerm(poly, new PolynomialTerm(polynomialTerms[i]));
		}
		return poly;
	}
	
	/**
	 * Auxiliary polynomial term that represents an error during the translation process, e.g., if original term had wrong sorts.
	 */
	public PolynomialTerm() {
		super(0);
		mTerm2Coefficient = null;
		mConstant = null;
		mSort = null;
	}

	/**
	 * True if this represents not an polynomial or affine term but an error during the translation process, e.g., if original term
	 * had wrong sorts.
	 */
	public boolean isErrorTerm() {
		if (mTerm2Coefficient == null) {
			assert mConstant == null;
			assert mSort == null;
			return true;
		} else {
			assert mConstant != null;
			assert mSort != null;
			return false;
		}
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
	 * Transforms this PolynomialTerm into a Term that is supported by the solver.
	 *
	 * @param script
	 *            Script for that this term is constructed.
	 */
	public Term toTerm(final Script script) {
		if (isLinear()) {
			return affineToTerm(script);
		}
		return polynomialToTerm(script);
	}
	
	/**
	 * The transformation to a Term for affineTerms.
	 */
	private Term affineToTerm(final Script script) {
		Term[] summands;
		if (mConstant.equals(Rational.ZERO)) {
			summands = new Term[getVariable2Coefficient().size()];
		} else {
			summands = new Term[getVariable2Coefficient().size() + 1];
		}
		int i = 0;
		for (final Map.Entry<Term, Rational> entry : getVariable2Coefficient().entrySet()) {
			assert !entry.getValue().equals(Rational.ZERO) : "zero is no legal coefficient in AffineTerm";
			if (entry.getValue().equals(Rational.ONE)) {
				summands[i] = entry.getKey();
			} else {
				final Term coeff = SmtUtils.rational2Term(script, entry.getValue(), mSort);
				summands[i] = SmtUtils.mul(script, mSort, coeff, entry.getKey());
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
	
	/**
	 * The transformation to a Term for polynomialTerms.
	 */
	private Term polynomialToTerm(final Script script) {
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
	
	/**
	 * @return unmodifiable map where each variable (wrapped as Monomial) is mapped to its coefficient.
	 */
	public Map<Monomial, Rational> getMonomial2Coefficient() {
		if (!isLinear()) {
			return Collections.unmodifiableMap(castMonomialMap(mTerm2Coefficient));
		}
		return Collections.unmodifiableMap(turnVariableMapIntoMonomialMap(castVariableMap(mTerm2Coefficient)));
	}
	
	/**
	 * @return unmodifiable map where each variable is mapped to its coefficient.
	 */
	public Map<Term, Rational> getVariable2Coefficient() {
		if (isLinear()) {
			return Collections.unmodifiableMap(castVariableMap(mTerm2Coefficient));
		}
		throw new UnsupportedOperationException("Term is not linear. Use getMonomial2Coefficient() instead.");
	}
	
	/**
	 * @return whether this polynomial term is just a constant
	 */
	public boolean isConstant() {
		if (mTerm2Coefficient instanceof Map<?, ?>) {
			return ((Map<?, ?>) mTerm2Coefficient).isEmpty();
		}
		throw new UnsupportedOperationException("You may not ask this, when the Map is no Map (e. g. ErrorTerm)");
	}

	/**
	 * Return true, when this term is linear (thus could be represented by AffineTerm), false otherwise.
	 */
	public boolean isLinear() {
		if (isConstant()) {
			return true;
		}
		Monomial maybeMonomial = (Monomial) ((Map<?, ?>) mTerm2Coefficient).keySet().iterator().next();
		//This is sufficient because of our convention of the two possible states of the map:
		//Monomial2Coefficient or Variable2Coefficient. Breaking this convention will lead to numerous bugs!!!!
		if (maybeMonomial instanceof Monomial) {
			return false;
		}else {
			return true;
		}
	}
	
	/**
	 * This is a method that performs an unsafe cast to retrieve a Monomial to Rational Map
	 * from the mTerm2Coefficient-object
	 */
	@SuppressWarnings("unchecked")
	private Map<Monomial, Rational> castMonomialMap(Object map){
		if (mTerm2Coefficient instanceof Map<?, ?>) {
			return (Map<Monomial, Rational>) mTerm2Coefficient;
		}
		throw new UnsupportedOperationException("You may not ask for this, when there is no Map (e. g. ErrorTerm)");
	}
	
	/**
	 * This is a method that performs an unsafe cast to retrieve a Term (Variable) to Rational Map
	 * from the mTerm2Coefficient-object.
	 */
	@SuppressWarnings("unchecked")
	private Map<Term, Rational> castVariableMap(Object map){
		if (mTerm2Coefficient instanceof Map<?, ?>) {
			return (Map<Term, Rational>) mTerm2Coefficient;
		}
		throw new UnsupportedOperationException("You may not ask for this, when there is no Map (e. g. ErrorTerm)");
	}
	
	/**
	 * Given a Variable2Coefficients-map, this turns it into a Monomial2Coefficients-map.
	 */
	private Map<Monomial, Rational> turnVariableMapIntoMonomialMap(Map<Term, Rational> termMap){
		switch (termMap.size()) {
		case 0:
			return Collections.emptyMap();
		case 1:
			Map.Entry<Term, Rational> singleEntry = termMap.entrySet().iterator().next();
			return Collections.singletonMap(new Monomial(singleEntry.getKey(), Rational.ONE), singleEntry.getValue());
		default:
			Map<Monomial, Rational> MonoMap = new HashMap<>();
			for (final Map.Entry<Term, Rational> entry : termMap.entrySet()) {
				if (entry.getKey() instanceof Monomial) {
					throw new IllegalArgumentException("This map has monomials in it. Something before went wrong!");
				}
				MonoMap.put(new Monomial(entry.getKey(),  Rational.ONE), entry.getValue());
			}
			return MonoMap;
			}
	}
	
	/**
	 * @return whether this polynomial term is zero
	 */
	public boolean isZero() {
		if (mTerm2Coefficient instanceof Map<?, ?>) {
			return mConstant.equals(Rational.ZERO) && ((Map<?, ?>) mTerm2Coefficient).isEmpty();
		}
		throw new UnsupportedOperationException("You may not ask this, when the Map is no Map (e. g. ErrorTerm)");
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

	@Override
	public Sort getSort() {
		return mSort;
	}
	
	@Override
	public void toStringHelper(final ArrayDeque<Object> mTodo) {
		throw new UnsupportedOperationException("This is an auxilliary Term and not supported by the solver");
	}
	
	public static PolynomialTerm applyModuloToAllCoefficients(final Script script, final PolynomialTerm polynomialTerm,
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
		result = prime * result + (mTerm2Coefficient == null ? 0 : mTerm2Coefficient.hashCode());
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
		if (mTerm2Coefficient == null) {
			if (other.mTerm2Coefficient != null) {
				return false;
			}
		} else if (!mTerm2Coefficient.equals(other.mTerm2Coefficient)) {
			return false;
		}
		return true;
	}
}