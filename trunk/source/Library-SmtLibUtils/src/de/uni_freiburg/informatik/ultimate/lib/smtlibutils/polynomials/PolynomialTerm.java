package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTermUtils.GeneralizedConstructor;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.SparseMapBuilder;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

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
 * @author Leonard Fichtner (leonard.fichtner@web.de)
 *
 */
public class PolynomialTerm extends AbstractGeneralizedAffineTerm<Monomial> {

	/**
	 * Constructor to be used of all static methods that construct a polynomialTerm.
	 */
	public PolynomialTerm(final Sort s, final Rational constant, final Map<Monomial, Rational> map) {
		super(s, constant, map);
		assert !PolynomialTermUtils.isAffineMap(map) : "This PolynomialTerm can be represented as an AffineTerm!";
	}

	/**
	 * Auxiliary polynomial term that represents an error during the translation
	 * process, e.g., if original term had wrong sorts.
	 */
	public PolynomialTerm() {
		super();
	}

	@Override
	protected IPolynomialTerm constructNew(final Sort sort, final Rational constant,
			final Map<Monomial, Rational> variables2coeffcient) {
		return PolynomialTerm.minimalRepresentation(sort, constant, variables2coeffcient);
	}

	@Override
	protected Monomial constructAbstractVar(final Term term) {
		return new Monomial(term, Rational.ONE);
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
	 * Returns a new PolynomialTerm that represents the product of polynomialTerm
	 * and multiplier.
	 */
	public static AbstractGeneralizedAffineTerm<?> mul(final IPolynomialTerm polynomialTerm,
			final Rational multiplier) {
		final GeneralizedConstructor<Monomial, AbstractGeneralizedAffineTerm<?>> constructor = PolynomialTerm::minimalRepresentation;
		return PolynomialTermUtils.constructMul(x -> ((PolynomialTerm) x).getMonomial2Coefficient(), constructor,
				polynomialTerm, multiplier);
	}

	/**
	 * The given arguments specify a Term. This constructor determines whether it
	 * must be represented by the PolynomialTerm class, or if the AffineTerm class
	 * is sufficient (more storage efficiency). Afterwards it returns this Term
	 * represented by one of the two classes, chosen accordingly.
	 */
	private static AbstractGeneralizedAffineTerm<?> minimalRepresentation(final Sort sort, final Rational coeff,
			final Map<Monomial, Rational> map) {
		if (PolynomialTermUtils.isAffineMap(map)) {
			return new AffineTerm(sort, coeff, PolynomialTermUtils.convertToAffineMap(map));
		}
		return new PolynomialTerm(sort, coeff, map);
	}

	/**
	 * Returns a new PolynomialTerm that represents the product of two
	 * polynomialTerms.
	 */
	public static IPolynomialTerm mulPolynomials(final IPolynomialTerm poly1, final IPolynomialTerm poly2) {
		final Sort s = poly1.getSort();
		final Rational coeff = calculateProductCoefficient(poly1, poly2);
		final Map<Monomial, Rational> polyMap = calculateProductMap(poly1, poly2);
		return minimalRepresentation(s, coeff, polyMap);
	}

	/**
	 * Calculate the Coefficient of the product of two polynomials.
	 */
	private static Rational calculateProductCoefficient(final IPolynomialTerm poly1, final IPolynomialTerm poly2) {
		Rational newCoeff;
		if (SmtSortUtils.isBitvecSort(poly1.getSort())) {
			newCoeff = PolynomialTermUtils.bringValueInRange(poly1.getConstant().mul(poly2.getConstant()),
					poly1.getSort());
		} else {
			newCoeff = poly1.getConstant().mul(poly2.getConstant());
		}
		return newCoeff;
	}

	/**
	 * Calculate the map of the product of two polynomials (in Monomial2Coefficient
	 * form).
	 */
	private static Map<Monomial, Rational> calculateProductMap(final IPolynomialTerm poly1,
			final IPolynomialTerm poly2) {
		final SparseMapBuilder<Monomial, Rational> mapBuilder = new SparseMapBuilder<>();
		monoTimesMonoIntoMap(mapBuilder, poly1, poly2);
		monomialsTimesConstantIntoMap(mapBuilder, poly1, poly2);
		monomialsTimesConstantIntoMap(mapBuilder, poly2, poly1);
		return mapBuilder.getBuiltMap();
	}

	/**
	 * Multiply just the Monomials of the two polynomialTerms with each other and
	 * put them into the given map. Return that same map.
	 */
	private static SparseMapBuilder<Monomial, Rational> monoTimesMonoIntoMap(
			final SparseMapBuilder<Monomial, Rational> builder, final IPolynomialTerm poly1,
			final IPolynomialTerm poly2) {
		for (final Map.Entry<Monomial, Rational> summand1 : poly1.getMonomial2Coefficient().entrySet()) {
			for (final Map.Entry<Monomial, Rational> summand2 : poly2.getMonomial2Coefficient().entrySet()) {
				final Monomial mono = new Monomial(summand1.getKey(), summand2.getKey());
				final Rational tempCoeff;
				final Rational newCoeff;
				final Rational coeff = builder.get(mono);

				// Check whether this Monomial does already exist in the map
				if (coeff == null) {
					tempCoeff = summand1.getValue().mul(summand2.getValue());
				} else {
					tempCoeff = summand1.getValue().mul(summand2.getValue()).add(coeff);
				}

				if (SmtSortUtils.isBitvecSort(poly1.getSort())) {
					newCoeff = PolynomialTermUtils.bringValueInRange(tempCoeff, poly1.getSort());
				} else {
					newCoeff = tempCoeff;
				}

				if (!newCoeff.equals(Rational.ZERO)) {
					builder.put(mono, newCoeff);
				}
			}
		}
		return builder;
	}

	/**
	 * Multiply the Monomials of poly1 with the constant of poly2 and put them into
	 * the given map. Return that same map.
	 */
	private static SparseMapBuilder<Monomial, Rational> monomialsTimesConstantIntoMap(
			final SparseMapBuilder<Monomial, Rational> builder, final IPolynomialTerm poly1,
			final IPolynomialTerm poly2) {
		for (final Map.Entry<Monomial, Rational> summand : poly1.getMonomial2Coefficient().entrySet()) {
			final Rational coeff = builder.get(summand.getKey());
			final Rational newCoeff;
			final Rational tempCoeff;

			// Check whether this Monomial does already exist in the map
			if (coeff == null) {
				tempCoeff = summand.getValue().mul(poly2.getConstant());
			} else {
				tempCoeff = summand.getValue().mul(poly2.getConstant()).add(coeff);
			}

			if (SmtSortUtils.isBitvecSort(poly1.getSort())) {
				newCoeff = PolynomialTermUtils.bringValueInRange(tempCoeff, poly1.getSort());
			} else {
				newCoeff = tempCoeff;
			}

			if (!newCoeff.equals(Rational.ZERO)) {
				builder.put(summand.getKey(), newCoeff);
			}
		}
		return builder;
	}

	/**
	 * Returns the sum of given polynomials.
	 */
	public static AbstractGeneralizedAffineTerm<?> sum(final IPolynomialTerm... summands) {
		final GeneralizedConstructor<Monomial, AbstractGeneralizedAffineTerm<?>> constructor = PolynomialTerm::minimalRepresentation;
		return PolynomialTermUtils.constructSum(PolynomialTerm::termWrapper, constructor, summands);
	}

	private static Map<Monomial, Rational> termWrapper(final IPolynomialTerm poly) {
		if (poly.isAffine()) {
			final SparseMapBuilder<Monomial, Rational> mapBuilder = new SparseMapBuilder<>();
			for (final Entry<Term, Rational> var2coeff : ((AffineTerm) poly).getVariable2Coefficient().entrySet()) {
				mapBuilder.put(new Monomial(var2coeff.getKey(), Rational.ONE), var2coeff.getValue());
			}
			return mapBuilder.getBuiltMap();
		} else {
			return ((PolynomialTerm) poly).getMonomial2Coefficient();
		}
	}

	/**
	 * Returns a PolynomialTerm which represents the quotient of the given arguments
	 * (see {@PolynomialTermTransformer #divide(Sort, IPolynomialTerm[])}).
	 */
	public static IPolynomialTerm divide(final IPolynomialTerm[] polynomialTerms, final Script script) {
		if (!divisionPossible(polynomialTerms)) {
			// In case we cannot handle this division properly (e.g. dividing by variables)
			// we treat this
			// whole term as an unique variable.
			return PolynomialTermUtils.simplifyImpossibleDivision("/", polynomialTerms, script);
		}
		return constructDivision(polynomialTerms, script);
	}

	/**
	 * Returns a PolynomialTerm which represents the integral quotient of the given
	 * arguments (see {@PolynomialTermTransformer #div(Sort, IPolynomialTerm[])}).
	 */
	public static IPolynomialTerm div(final IPolynomialTerm[] polynomialArgs, final Script script) {
		if (!divisionPossible(polynomialArgs)) {
			// In case we cannot handle this division properly (e.g. dividing by variables)
			// we treat this
			// whole term as an unique variable.
			return PolynomialTermUtils.simplifyImpossibleDivision("div", polynomialArgs, script);
		}
		final IPolynomialTerm result = constructDivision(polynomialArgs, script);
		if (result.isIntegral()) {
			return result;
		}
		return PolynomialTermUtils.simplifyImpossibleDivision("div", polynomialArgs, script);
	}

	/**
	 * Given an array of polynomialTerms, this determines whether a division is
	 * actually possible at the moment. If it is return true, false otherwise.
	 */
	public static boolean divisionPossible(final IPolynomialTerm[] polynomialTerms) {
		for (int i = 1; i < polynomialTerms.length; i++) {
			if (!polynomialTerms[i].isConstant() || polynomialTerms[i].isZero()) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Construct the division of the given polynomialTerms.
	 */
	private static IPolynomialTerm constructDivision(final IPolynomialTerm[] polynomialTerms, final Script script) {
		IPolynomialTerm poly = PolynomialTerm.mul(polynomialTerms[0], polynomialTerms[1].getConstant().inverse());
		for (int i = 2; i < polynomialTerms.length; i++) {
			poly = PolynomialTerm.mul(poly, polynomialTerms[i].getConstant().inverse());
		}
		return poly;
	}

	@Override
	protected Term abstractVariableToTerm(final Script script, final Monomial abstractVariable) {
		return abstractVariable.toTerm(script);
	}

	@Override
	protected Term abstractVariableTimesCoeffToTerm(final Script script, final Monomial abstractVariable, final Rational coeff) {
		return abstractVariable.timesCoefficientToTerm(script, coeff);
	}

	public static PolynomialTerm applyModuloToAllCoefficients(final PolynomialTerm polynomialTerm,
			final BigInteger divident) {
		final GeneralizedConstructor<Monomial, PolynomialTerm> constructor = PolynomialTerm::new;
		return PolynomialTermUtils.applyModuloToAllCoefficients(polynomialTerm, divident, constructor);
	}

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
		for (final Monomial mono : getMonomial2Coefficient().keySet()) {
			if (mono.isVariable(var)) {
				return true;
			}
		}
		return false;
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

	@Override
	protected Pair<Rational, Rational> computeMinMax() {
		// TODO implement for analogously to method in AffineTerm,
		// helps only if all variables in all all monomials are variables
		return null;
	}

	@Override
	public AbstractGeneralizedAffineTerm<?> removeAndNegate(final Monomial monomialOfSubject) {
		boolean allMonomialsAreLinear = true;
		final HashMap<Monomial, Rational> newAbstractVariable2Coefficient = new HashMap<>();
		for (final Entry<Monomial, Rational> entry : mAbstractVariable2Coefficient.entrySet()) {
			if (!entry.getKey().equals(monomialOfSubject)) {
				newAbstractVariable2Coefficient.put(entry.getKey(), entry.getValue().negate());
				if (!entry.getKey().isLinear()) {
					allMonomialsAreLinear = false;
				}
			}
		}
		if (allMonomialsAreLinear) {
			final Map<Term, Rational> map = newAbstractVariable2Coefficient.entrySet().stream().collect(Collectors.toMap(x -> x.getKey().getSingleVariable(), x -> x.getValue()));
			return new AffineTerm(getSort(), getConstant().negate(), map);
		} else {
			return new PolynomialTerm(getSort(), getConstant().negate(), newAbstractVariable2Coefficient);
		}
	}

	@Override
	public PolynomialTerm divInvertible(final Rational divisor) {
		final HashMap<Monomial, Rational> newAbstractVariable2Coefficient = new HashMap<>();
		for (final Entry<Monomial, Rational> entry : mAbstractVariable2Coefficient.entrySet()) {
			final Rational newCoefficient = PolynomialTermUtils.divInvertible(getSort(), entry.getValue(), divisor);
			if (newCoefficient == null) {
				return null;
			} else {
				newAbstractVariable2Coefficient.put(entry.getKey(), newCoefficient);
			}
		}
		final Rational newConstant = PolynomialTermUtils.divInvertible(getSort(), getConstant(), divisor);
		return new PolynomialTerm(getSort(), newConstant, newAbstractVariable2Coefficient);
	}

}