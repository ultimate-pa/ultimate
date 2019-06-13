package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.PolynomialTermUtils.GeneralizedConstructor;

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
public class PolynomialTerm extends AbstractGeneralizedAffineTerm<Monomial> implements IPolynomialTerm {

	/**
	 * Constructor to be used of all static methods that construct a polynomialTerm.
	 */
	public PolynomialTerm(final Sort s, final Rational constant, final Map<Monomial, Rational> map) {
		super(s, constant, map);
	}

	/**
	 * Check if term is of a type that may be a variable of an PolynomialTerm.
	 */
	@Override
	public void checkIfTermIsLegalVariable(final Term term) {
		if (term instanceof TermVariable || term instanceof ApplicationTerm) {
			// term is ok
		} else {
			throw new IllegalArgumentException("Variable of PolynomialTerm has to be TermVariable or ApplicationTerm");
		}
	}

	/**
	 * Returns a new PolynomialTerm that represents the product of polynomialTerm and multiplier.
	 */
	public static PolynomialTerm mul(final IPolynomialTerm polynomialTerm,
									 final Rational multiplier) {
		final GeneralizedConstructor<Monomial, PolynomialTerm> constructor = PolynomialTerm::new;
		return PolynomialTermUtils.constructMul(x -> ((PolynomialTerm) x).getMonomial2Coefficient(), constructor,
				polynomialTerm, multiplier);
	}

	//TODO: Ask Matthias where assert poly1.getSort() == poly2.getSort(); should be put. Highest level? Only on Multiplication?
	/**
	 * Returns a new PolynomialTerm that represents the product of two polynomialTerms.
	 */
	public static PolynomialTerm mulPolynomials(final IPolynomialTerm poly1, final IPolynomialTerm poly2) {
		assert poly1.getSort() == poly2.getSort();
		return new PolynomialTerm(poly1.getSort(),
				  				  calculateProductCoefficient(poly1, poly2),
				  				  calculateProductMap(poly1, poly2));
	}

	
	/**
	 * Calculate the Coefficient of the product of two polynomials.
	 */
	private static Rational calculateProductCoefficient(final IPolynomialTerm poly1, final IPolynomialTerm poly2) {
		Rational newCoeff;
		if (SmtSortUtils.isBitvecSort(poly1.getSort())) {
			newCoeff = PolynomialTermUtils.bringValueInRange(poly1.getConstant().mul(poly2.getConstant()),
															 poly1.getSort());
		}else {
			newCoeff = poly1.getConstant().mul(poly2.getConstant());
		}
		return newCoeff;
	}
	
	/**
	 * Calculate the map of the product of two polynomials (in Monomial2Coefficient form).
	 */
	private static Map<Monomial, Rational> calculateProductMap(final IPolynomialTerm poly1, final IPolynomialTerm poly2){
		final Map<Monomial, Rational> map = new HashMap<>();
		monomialsTimesMonomialsIntoMap(map, poly1, poly2);
		monomialsTimesConstantIntoMap(map, poly1, poly2);
		monomialsTimesConstantIntoMap(map, poly2, poly1);
		return PolynomialTermUtils.shrinkMap(map);
	}

	/**
	 * Multiply just the Monomials of the two polynomialTerms with each other and put them into the given map.
	 * Return that same map.
	 */
	private static Map<Monomial, Rational> monomialsTimesMonomialsIntoMap(final Map<Monomial, Rational> map,
																  		  final IPolynomialTerm poly1,
																  		  final IPolynomialTerm poly2){
		for (final Map.Entry<Monomial, Rational> summand1 : poly1.getMonomial2Coefficient().entrySet()) {
			for (final Map.Entry<Monomial, Rational> summand2 : poly2.getMonomial2Coefficient().entrySet()) {
				final Monomial mono = new Monomial(summand1.getKey(),summand2.getKey());
				final Rational newCoeff;
				final Rational coeff = map.get(mono);
				if (coeff == null) {
					newCoeff = summand1.getValue().mul(summand2.getValue());
					map.put(mono, newCoeff);
				}else {
					//TODO: Write Tests for Bitvectors.
					if (SmtSortUtils.isBitvecSort(poly1.getSort())) {
						newCoeff = PolynomialTermUtils.bringValueInRange(summand1.getValue().mul(summand2.getValue()).add(coeff),
																		 poly1.getSort());
					}else {
						newCoeff = summand1.getValue().mul(summand2.getValue()).add(coeff);
					}
					if (newCoeff.equals(Rational.ZERO)) {
						map.remove(mono);
					}else {
						map.put(mono, newCoeff);
					}
				}
			}
		}
		return map;
	}

	/**
	 * Multiply the Monomials of poly1 with the constant of poly2 and put them into the given map.
	 * Return that same map.
	 */
	private static Map<Monomial, Rational> monomialsTimesConstantIntoMap(final Map<Monomial, Rational> map,
																  		final IPolynomialTerm poly1,
																  		final IPolynomialTerm poly2){
		for (final Map.Entry<Monomial, Rational> summand : poly1.getMonomial2Coefficient().entrySet()) {
			final Rational coeff = map.get(summand.getKey());
			final Rational newCoeff;
			if (coeff == null) {
				newCoeff = summand.getValue().mul(poly2.getConstant());
				if (!newCoeff.equals(Rational.ZERO)) {
					map.put(summand.getKey(), newCoeff);
				}
			}else {
				if (SmtSortUtils.isBitvecSort(poly1.getSort())) {
					newCoeff = PolynomialTermUtils.bringValueInRange(summand.getValue().mul(poly2.getConstant()).add(coeff),
																	 poly1.getSort());
				}else {
					newCoeff = summand.getValue().mul(poly2.getConstant()).add(coeff);
				}
				if (!newCoeff.equals(Rational.ZERO)) {
					map.put(summand.getKey(), newCoeff);
				}
			}
		}
		return map;
	}

	/**
	 * Returns the sum of given polynomials.
	 */
	public static PolynomialTerm sum(final IPolynomialTerm... summands) {
		final GeneralizedConstructor<Monomial, PolynomialTerm> constructor = PolynomialTerm::new;
		return PolynomialTermUtils.constructSum(x -> ((PolynomialTerm) x).getMonomial2Coefficient(), constructor, summands);
	}

	/**
	 * Auxiliary polynomial term that represents an error during the translation process, e.g., if original term had wrong sorts.
	 */
	public PolynomialTerm() {
		super();
	}

	@Override
	protected Term abstractVariableToTerm(final Script script, final Monomial abstractVariable) {
		return abstractVariable.toTerm(script);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.IPolynomialTerm#getMonomial2Coefficient()
	 */
	@Override
	public Map<Monomial, Rational> getMonomial2Coefficient() {
		return mAbstractVariable2Coefficient;
	}

	/**
	 * @return true iff var is a variable of this {@link PolynomialTerm} (i.e., if
	 *         var is a variable of some {@link Monomial} that has a non-zero
	 *         coefficient) Note that for returning true it is especially NOT
	 *         sufficient if var occurs only as a subterm of some variable.
	 */
	@Override
	public boolean isVariable(final Term var) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isAffine() {
		return false;
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

}