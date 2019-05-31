package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms;

import java.math.BigInteger;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.BitvectorUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant;

/**
 * Transforms a {@link Term} which is "polynomial" into our {@link PolynomialTerm} data
 * structure. The result is an auxiliary error term if the input was not polynomial.
 *
 * The transformation is done by an recursive algorithm. However, in order to
 * circumvent the problem that the performance of Java virtual machines is
 * rather poor for recursive methods calls we implement the algorithm by using
 * our {@link TermTransformer}. The {@link TermTransformer} allows us to
 * implement recursive algorithms for {@link Term}s without recursive methods
 * calls by explicitly using a stack.
 *
 * @author Leonard Fichtner
 *
 */
public class PolynomialTermTransformer extends TermTransformer {

	private final Script mScript;

	/**
	 * Predicate that defines which Terms might be variables of the
	 * {@link PolynomialTerm}. Currently, every {@link TermVariable} and every
	 * {@link ApplicationTerm} can be a variable of the result. In
	 * the future this may become a parameter in order to allow users
	 * of this class to be more restrictive.
	 */
	private final Predicate<Term> mIsPolynomialVariable = (x -> ((x instanceof TermVariable)
			|| (x instanceof ApplicationTerm)));

	public PolynomialTermTransformer(final Script script) {
		mScript = script;
	}

	@Override
	protected void convert(final Term term) {
		// If the term has a sort that is not supported, we report
		// that the input cannot be converted into a PolynomialTerm.
		// This is implemented by returning an special kind
		// of PolynomialTerm.
		if (!hasSupportedSort(term)) {
			inputIsNotPolynomial();
			return;
		}
		// Otherwise, if the terms represents a literal, we convert the literal
		// to a PolynomialTerm and tell the TermTransformer that this
		// is the result (i.e., it should not descend to subformulas).
		final Rational valueOfLiteral = tryToConvertToLiteral(mScript, term);
		if (valueOfLiteral != null) {
			final AffineTerm result = AffineTerm.constructConstant(term.getSort(), valueOfLiteral);
			setResult(result);
			return;
		}
		// Otherwise, if the term represents an "polynomial function" we tell
		// TermTransformer to descend to subformulas.
		if (isPolynomialFunction(term)) {
			super.convert(term);
			return;
		}
		// Otherwise, the term is considered as a variable of our PolynomialTerms,
		// we construct an PolynomialTerm that represents a variable and tell the
		// TermTransformer that this
		// is the result (i.e., it should not descend to subformulas).
		if (mIsPolynomialVariable.test(term)) {
			final AffineTerm result = new AffineTerm(term);
			setResult(result);
			return;
		}
		// Otherwise, the input cannot be converted to an PolynomialTerm.
		inputIsNotPolynomial();
		return;
	}

	/**
	 * Sets result to auxiliary error term.
	 */
	private void inputIsNotPolynomial() {
		setResult(new PolynomialTerm());
	}

	/**
	 * Currently, we support the SMT {@link Sort}s Int and Real (called numeric
	 * sorts) and the bitvector sorts.
	 */
	private static boolean hasSupportedSort(final Term term) {
		return SmtSortUtils.isNumericSort(term.getSort()) || SmtSortUtils.isBitvecSort(term.getSort());
	}

	/**
	 * Check if term is an {@link ApplicationTerm} whose {@link FunctionSymbol}
	 * represents an "polynomial function". We call a function an "polynomial function" if
	 * it implements an addition, subtraction, multiplication, or real number
	 * division.
	 */
	private static boolean isPolynomialFunction(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			return isPolynomialFunctionSymbol(appTerm.getFunction().getName());
		} else {
			return false;
		}
	}

	private static boolean isPolynomialFunctionSymbol(final String funName) {
		return (funName.equals("+") || funName.equals("-") || funName.equals("*") || funName.equals("/")
				|| funName.equals("bvadd") || funName.equals("bvsub") || funName.equals("bvmul"));
	}

	/**
	 * Check if term represents a literal. If this is the case, then return its
	 * value as a {@link Rational} otherwise return true.
	 */
	private static Rational tryToConvertToLiteral(final Script script, final Term term) {
		final Rational result;
		if (SmtSortUtils.isBitvecSort(term.getSort())) {
			final BitvectorConstant bc = BitvectorUtils.constructBitvectorConstant(term);
			if (bc != null) {
				result = Rational.valueOf(bc.getValue(), BigInteger.ONE);
			} else {
				result = null;
			}
		} else if (SmtSortUtils.isNumericSort(term.getSort())) {
			if (term instanceof ConstantTerm) {
				result = SmtUtils.convertConstantTermToRational((ConstantTerm) term);
			} else {
				result = null;
			}
		} else {
			result = null;
		}
		return result;
	}

	//TODO: Change PolynomialTermTransformer to use the more efficient class AffineTerm if possible.
	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
		// This method is called for every subformula for which we let the
		// TermTransformer descend to subformulas.
		// Here, the arguments are the result of the "recursive" calls for the
		// subformulas.
		assert (isPolynomialFunctionSymbol(appTerm.getFunction().getName())) : "We only descended for polynomial functions";
		// First, we check if some of this arguments is the auxiliary error term.
		// If this is the case, we report that input is not polynomial.
		final IPolynomialTerm[] polynomialArgs = castAndCheckForNonPolynomialArguments(newArgs);
		if (polynomialArgs == null) {
			inputIsNotPolynomial();
			return;
		}
		final String funName = appTerm.getFunction().getName();
		if (funName.equals("*") || funName.equals("bvmul")) {
			final Sort sort = appTerm.getSort();
			final IPolynomialTerm result = multiply(sort, polynomialArgs);
			castAndSetResult(result);
			return;
		} else if (funName.equals("+") || funName.equals("bvadd")) {
			final IPolynomialTerm result = add(polynomialArgs);
			castAndSetResult(result);
			return;
		} else if (funName.equals("-") || funName.equals("bvsub")) {
			final IPolynomialTerm result;
			if (polynomialArgs.length == 1) {
				// unary minus
				result = negate(polynomialArgs[0]);
			} else {
				result = subtract(polynomialArgs);
			}
			castAndSetResult(result);
			return;
		} else if (funName.equals("/")) {
			final Sort sort = appTerm.getSort();
			final IPolynomialTerm result = divide(sort, polynomialArgs);
			if (result.isErrorTerm()) {
				inputIsNotPolynomial();
				return;
			}
			castAndSetResult(result);
			return;
		} else {
			throw new UnsupportedOperationException("unsupported symbol " + funName);
		}
	}

	/**
	 * Cast the interface IPolynomialTerm in a way that the TermTransformer
	 * accepts the result for "setResult". Execute "setResult" afterwards.
	 */
	private void castAndSetResult(final IPolynomialTerm poly){
		if (poly instanceof PolynomialTerm) {
			setResult((PolynomialTerm) poly);
			return;
		}else if(poly instanceof AffineTerm) {
			setResult((AffineTerm) poly);
			return;
		}
		throw new UnsupportedOperationException("This IPolynomialTerm is instance of no known class.");
	}

	/**
	 * Multiply an array of PolynomialTerms.
	 */
	private static IPolynomialTerm multiply(final Sort sort, final IPolynomialTerm[] polynomialArgs) {
		//TODO: Find out whether passing the sort explicitly in case every polynomialTerm is just a Constant
		//is really necessary (like in the AffineTermTransformer): YES it is in case that the array is empty
		//TODO: Ask Matthias why does AffineTermTransformer not catch this in add?
		if (polynomialArgs.length == 0) {
			return PolynomialTerm.polynomialOfRational(sort, Rational.ONE);
		}
		if (polynomialArgs.length == 1) {
			return polynomialArgs[0];
		}

		IPolynomialTerm poly = multiplyTwoPolynomials(polynomialArgs[0], polynomialArgs[1]);
		for (int i = 2; i < polynomialArgs.length; i++) {
			poly = multiplyTwoPolynomials(poly, polynomialArgs[i]);
		}
		return poly;
	}

	/**
	 * Returns the product of poly1 and poly2.
	 */
	private static IPolynomialTerm multiplyTwoPolynomials(final IPolynomialTerm poly1, final IPolynomialTerm poly2) {
		assert poly1.getSort() == poly2.getSort();

		if (productWillBePolynomial(poly1, poly2)) {
			return PolynomialTerm.polynomialTimesPolynomial(poly1, poly2);
		}else {
			return AffineTerm.construct(poly1.getSort(),
								  poly1.getConstant().mul(poly2.getConstant()),
								  calculateProductMapOfAffineTerms(poly1, poly2));
		}
	}

	/**
	 * Determines whether the product of two polynomialTerms will be truly polynomial (not affine).
	 * If the result is truly polynomial it returns true, false otherwise.
	 */
	private static boolean productWillBePolynomial(final IPolynomialTerm poly1, final IPolynomialTerm poly2) {
		return !poly1.isAffine() || !poly2.isAffine() || (!poly1.isConstant() && !poly2.isConstant());
	}

	/**
	 * Calculate the map of the product of affineTerms (in Variable2Coefficient form).
	 */
	private static Map<Term, Rational> calculateProductMapOfAffineTerms(final IPolynomialTerm poly1, final IPolynomialTerm poly2){
		final Map<Term, Rational> map = new HashMap<>();
		if (poly1.isConstant()) {
			if (poly1.getConstant().equals(Rational.ZERO)) {
				return Collections.emptyMap();
			}
			for (final Map.Entry<Term, Rational> summand : ((AffineTerm) poly2).getVariable2Coefficient().entrySet()) {
				map.put(summand.getKey(), summand.getValue().mul(poly1.getConstant()));
			}
		//poly2 must be a constant then, or else the product will not be affine -> Error
		}else if (poly2.isConstant()){
			if (poly2.getConstant().equals(Rational.ZERO)) {
				return Collections.emptyMap();
			}
			for (final Map.Entry<Term, Rational> summand : ((AffineTerm) poly1).getVariable2Coefficient().entrySet()) {
				map.put(summand.getKey(), summand.getValue().mul(poly2.getConstant()));
			}
		}else {
			throw new UnsupportedOperationException("The outcome of this product is not affine!");
		}
		return shrinkMap(map);
	}

	/**
	 * Returns a shrinked version of a map if possible. Returns the given map otherwise.
	 */
	private static Map<Term, Rational> shrinkMap(final Map<Term, Rational> map){
		if (map.size() == 0) {
			return Collections.emptyMap();
		}
		else if (map.size() == 1) {
			final Entry<Term, Rational> entry = map.entrySet().iterator().next();
			return Collections.singletonMap(entry.getKey(), entry.getValue());
		}
		return map;
	}

	/**
	 * Construct a {@link PolynomialTerm} that is the sum of all inputs.
	 */
	private static IPolynomialTerm add(final IPolynomialTerm[] polynomialArgs) {
		if (someTermIsPolynomial(polynomialArgs)) {
			return PolynomialTerm.polynomialSum(polynomialArgs);
		}else {
			return AffineTerm.construct(polynomialArgs[0].getSort(),
								  calculateSumConstant(polynomialArgs),
								  calculateSumMapOfAffineTerms(polynomialArgs));
		}
	}

	/**
	 * Returns true when one of the given Terms is truly polynomial (not representable
	 * by an AffineTerm)
	 */
	private static boolean someTermIsPolynomial(final IPolynomialTerm...polynomialTerms) {
		for (final IPolynomialTerm polynomialTerm: polynomialTerms) {
			if (!polynomialTerm.isAffine()) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Calculate the constant of a sum of given IPolynomialTerms.
	 */
	private static Rational calculateSumConstant(final IPolynomialTerm...polynomialTerms) {
		Rational constant = Rational.ZERO;
		final Sort s = polynomialTerms[0].getSort();
		for (final IPolynomialTerm polynomialTerm : polynomialTerms) {
			if (SmtSortUtils.isBitvecSort(s)) {
				constant = bringValueInRange(constant.add(polynomialTerm.getConstant()), s);
			} else {
				constant = constant.add(polynomialTerm.getConstant());
			}
		}
		return constant;
	}

	private static Map<Term, Rational> calculateSumMapOfAffineTerms(final IPolynomialTerm... affineTerms){
		final Sort s = affineTerms[0].getSort();
		final Map<Term, Rational> map = new HashMap<>();
		for (final IPolynomialTerm affineTerm : affineTerms) {
			for (final Map.Entry<Term, Rational> summand : ((AffineTerm) affineTerm).getVariable2Coefficient().entrySet()) {
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
	 * Construct negation (unary minus).
	 */
	private static IPolynomialTerm negate(final IPolynomialTerm polynomialTerm) {
		if (polynomialTerm.isAffine()) {
			return new AffineTerm((AffineTerm) polynomialTerm, Rational.MONE);
		}
		return PolynomialTerm.polynomialTimesRational(polynomialTerm, Rational.MONE);
	}

	/**
	 * Given {@link PolynomialTerm}s <code>t1,t2,...,tn</code> construct an
	 * {@link PolynomialTerm} that represents the difference <code>t1-t2-...-tn</code>,
	 * i.e., the {@link PolynomialTerm} that is equivalent to
	 * <code>t1-(t2+...+tn)</code>
	 */
	private static IPolynomialTerm subtract(final IPolynomialTerm[] input) {
		assert input.length > 1;
		final IPolynomialTerm[] argumentsForSum = new IPolynomialTerm[input.length];
		// negate all arguments but the first (at position 0)
		argumentsForSum[0] = input[0];
		for (int i = 1; i < argumentsForSum.length; i++) {
			argumentsForSum[i] = negate(input[i]);
		}
		// construct the sum
		return add(argumentsForSum);
	}

	/**
	 * Given {@link PolynomialTerm}s <code>t1,t2,...,tn</code> construct an
	 * {@link PolynomialTerm} that represents the quotient <code>t1/t2/.../tn</code>,
	 * i.e., the {@link PolynomialTerm} that is equivalent to
	 * <code>t1*((1/t2)*...*(1/tn))</code>. Note that the function "/" is only
	 * defined the sort of reals. For integer division we have the function "div"
	 * which is currently not supported by our polynomial terms.
	 */
	private static IPolynomialTerm divide(final Sort sort, final IPolynomialTerm[] polynomialArgs) {
		assert SmtSortUtils.isRealSort(sort);
		if (polynomialArgs.length == 0) {
			return AffineTerm.constructConstant(sort, Rational.ONE);
		}else if (polynomialArgs.length == 1) {
			return polynomialArgs[0];
		}

		//Only Term at position 0 may be not affine.
		if (polynomialArgs[0].isAffine()) {
			return affineDivision(sort, polynomialArgs);
		}else {
			return polynomialDivision(polynomialArgs);
		}
	}

	/**
	 * Returns a PolynomialTerm which represents the quotient of the given arguments (see divide method above).
	 */
	private static IPolynomialTerm polynomialDivision(final IPolynomialTerm[] polynomialTerms) {
		for (int i = 1; i < polynomialTerms.length; i++) {
			if (!polynomialTerms[i].isConstant()) {
				throw new UnsupportedOperationException("Division by Variables not supported!");
			}
		}
		PolynomialTerm inverse = PolynomialTerm.polynomialOfRational(polynomialTerms[1].getSort(),
																	 polynomialTerms[1].getConstant().inverse());
		PolynomialTerm poly = PolynomialTerm.polynomialTimesPolynomial(polynomialTerms[0], inverse);
		for (int i = 2; i < polynomialTerms.length; i++) {
			inverse = PolynomialTerm.polynomialOfRational(polynomialTerms[i].getSort(),
					 polynomialTerms[i].getConstant().inverse());
			poly = PolynomialTerm.polynomialTimesPolynomial(poly, inverse);
		}
		return poly;
	}

	/**
	 * Returns an AffineTerm which represents the quotient of the given arguments (see divide method above).
	 */
	private static IPolynomialTerm affineDivision(final Sort sort, final IPolynomialTerm[] affineArgs) {
		final IPolynomialTerm affineTerm;
		Rational multiplier;
		if (affineArgs[0].isConstant()) {
			affineTerm = null;
			multiplier = affineArgs[0].getConstant();
		} else {
			affineTerm = affineArgs[0];
			multiplier = Rational.ONE;
		}
		final AffineTerm result;
		for (int i = 1; i < affineArgs.length; i++) {
			if (affineArgs[i].isConstant() && !affineArgs[i].isZero()) {
				multiplier = multiplier.mul(affineArgs[i].getConstant().inverse());
			} else {
				// Only the argument at position 0 may be a non-constant,
				// all other arguments must be literals,
				// divisors must not be zero.
				throw new UnsupportedOperationException("Division by Variables not supported!");
			}
		}
		if (affineTerm == null) {
			result = AffineTerm.constructConstant(sort, multiplier);
		} else {
			result = new AffineTerm((AffineTerm) affineTerm, multiplier);
		}
		return result;
	}

	//TODO: PolynomialRelation

	/**
	 * Convert an array of {@link Term}s into an an array of {@link PolynomialTerm}s by
	 * casting every single element. In case an element of the input is our
	 * auxiliary error term we return null instead.
	 */
	private static IPolynomialTerm[] castAndCheckForNonPolynomialArguments(final Term[] terms) {
		final IPolynomialTerm[] polynomialTerms = new IPolynomialTerm[terms.length];
		for (int i = 0; i < polynomialTerms.length; i++) {
			if (terms[i] instanceof IPolynomialTerm) {
				polynomialTerms[i] = (IPolynomialTerm) terms[i];
				if (polynomialTerms[i].isErrorTerm()) {
					return null;
				}
			} else {
				throw new AssertionError();
			}
		}
		return polynomialTerms;
	}
}
