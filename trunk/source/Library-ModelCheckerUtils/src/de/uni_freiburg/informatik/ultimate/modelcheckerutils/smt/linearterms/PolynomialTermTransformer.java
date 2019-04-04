package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms;

import java.math.BigInteger;
import java.util.function.Predicate;

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
			final AffineTerm result = new AffineTerm(term.getSort(), valueOfLiteral);
			setResult(result);
			return;
			//TODO: Change AffineTerm to PolynomialTerm
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
	 * represents an "affine function". We call a function an "affine function" if
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
	//TODO: AffineTerm shall inherit from PolynomialTermTransformer.
	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
		// This method is called for every subformula for which we let the
		// TermTransformer descend to subformulas.
		// Here, the arguments are the result of the "recursive" calls for the
		// subformulas.
		assert (isPolynomialFunctionSymbol(appTerm.getFunction().getName())) : "We only descended for polynomial functions";
		// First, we check if some of this arguments is the auxiliary error term.
		// If this is the case, we report that input is not polynomial.
		final PolynomialTerm[] polynomialArgs = castAndCheckForNonPolynomialArguments(newArgs);
		if (polynomialArgs == null) {
			inputIsNotPolynomial();
			return;
		}
		final String funName = appTerm.getFunction().getName();
		if (funName.equals("*") || funName.equals("bvmul")) {
			final Sort sort = appTerm.getSort();
			final PolynomialTerm result = multiply(polynomialArgs);
			setResult(result);
			return;
		} else if (funName.equals("+") || funName.equals("bvadd")) {
			final PolynomialTerm result = add(polynomialArgs);
			setResult(result);
			return;
		} else if (funName.equals("-") || funName.equals("bvsub")) {
			final PolynomialTerm result;
			if (polynomialArgs.length == 1) {
				// unary minus
				result = negate(polynomialArgs[0]);
			} else {
				result = subtract(polynomialArgs);
			}
			setResult(result);
			return;
		} else if (funName.equals("/")) {
			final Sort sort = appTerm.getSort();
			final PolynomialTerm result = divide(sort, polynomialArgs);
			if (result.isErrorTerm()) {
				inputIsNotPolynomial();
				return;
			}
			setResult(result);
			return;
		} else {
			throw new UnsupportedOperationException("unsupported symbol " + funName);
		}
	}
	
	/**
	 * Given {@link PolynomialTerm}s <code>t1,t2,...,tn</code> construct an
	 * {@link PolynomialTerm} that represents the quotient <code>t1/t2/.../tn</code>,
	 * i.e., the {@link PolynomialTerm} that is equivalent to
	 * <code>t1*((1/t2)*...*(1/tn))</code>. Note that the function "/" is only
	 * defined the sort of reals. For integer division we have the function "div"
	 * which is currently not supported by our polynomial terms.
	 */
	private static PolynomialTerm divide(final Sort sort, final PolynomialTerm[] polynomialArgs) {
		assert SmtSortUtils.isRealSort(sort);
		return PolynomialTerm.constructDivision(polynomialArgs);
	}
	
	/**
	 * Construct negation (unary minus).
	 */
	private static PolynomialTerm negate(final PolynomialTerm polynomialTerm) {
		return new PolynomialTerm(polynomialTerm, Rational.MONE);
	}
	
	/**
	 * Given {@link PolynomialTerm}s <code>t1,t2,...,tn</code> construct an
	 * {@link PolynomialTerm} that represents the difference <code>t1-t2-...-tn</code>,
	 * i.e., the {@link PolynomialTerm} that is equivalent to
	 * <code>t1-(t2+...+tn)</code>
	 */
	private static PolynomialTerm subtract(final PolynomialTerm[] input) {
		assert input.length > 1;
		final PolynomialTerm[] argumentsForSum = new PolynomialTerm[input.length];
		// negate all arguments but the first (at position 0)
		argumentsForSum[0] = input[0];
		for (int i = 1; i < argumentsForSum.length; i++) {
			argumentsForSum[i] = new PolynomialTerm(input[i], Rational.MONE);
		}
		// construct the sum
		return add(argumentsForSum);
	}
	
	/**
	 * Multiply an array of PolynomialTerms.
	 */
	private static PolynomialTerm multiply(final PolynomialTerm[] polynomialArgs) {
		//TODO: Find out whether passing the sort explicitly in case every polynomialTerm is just a Constant
		//is really necessary (like in the AffineTermTransformer): YES it is in case that the array is empty
		//TODO: catch empty arrays
		return PolynomialTerm.constructProduct(polynomialArgs);
	}
	
	//TODO: PolynomialRelation
	
	/**
	 * Construct an {@link PolynomialTerm} that is the sum of all inputs.
	 */
	private static PolynomialTerm add(final PolynomialTerm[] polynomialArgs) {
		return PolynomialTerm.constructAddition(polynomialArgs);
	}
	
	/**
	 * Convert an array of {@link Term}s into an an array of {@link PolynomialTerm}s by
	 * casting every single element. In case an element of the input is our
	 * auxiliary error term we return null instead.
	 */
	private static PolynomialTerm[] castAndCheckForNonPolynomialArguments(final Term[] terms) {
		final PolynomialTerm[] polynomialTerms = new PolynomialTerm[terms.length];
		for (int i = 0; i < polynomialTerms.length; i++) {
			if (terms[i] instanceof PolynomialTerm) {
				polynomialTerms[i] = (PolynomialTerm) terms[i];
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
