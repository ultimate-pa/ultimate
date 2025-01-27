package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials;

import java.util.Arrays;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Transforms a {@link Term} which is "polynomial" into our
 * {@link PolynomialTerm} data structure. The result is an auxiliary error term
 * if the input was not polynomial.
 *
 * The transformation is done by an recursive algorithm. However, in order to
 * circumvent the problem that the performance of Java virtual machines is
 * rather poor for recursive methods calls we implement the algorithm by using
 * our {@link TermTransformer}. The {@link TermTransformer} allows us to
 * implement recursive algorithms for {@link Term}s without recursive methods
 * calls by explicitly using a stack.
 *
 * @author Leonard Fichtner (leonard.fichtner@web.de)
 *
 */
public class PolynomialTermTransformer extends TermTransformer {

	private final Script mScript;

	/**
	 * Predicate that defines which Terms might be variables of the
	 * {@link PolynomialTerm}. Currently, every {@link TermVariable} and every
	 * {@link ApplicationTerm} can be a variable of the result. In the future this
	 * may become a parameter in order to allow users of this class to be more
	 * restrictive.
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
		final Rational valueOfLiteral = SmtUtils.tryToConvertToLiteral(term);
		if (valueOfLiteral != null) {
			final AffineTerm result = AffineTerm.constructConstant(term.getSort(), valueOfLiteral);
			setResult(result);
			return;
		}

		// When encountering a term of the form (* (div t1 t2) t2), we replace it by the term (- t1 (mod t1 t2)).
		// The class MulDivModRewriter ensures that TermTransformer descends into the subterms t1 and t2.
		final MulDivModRewriter mulDivModRewriter = MulDivModRewriter.forTerm(term);
		if (mulDivModRewriter != null) {
			mulDivModRewriter.run(this);
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
			final AffineTerm result = AffineTerm.constructVariable(term);
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
	 * represents an "polynomial function". We call a function an "polynomial
	 * function" if it implements an addition, subtraction, multiplication, or real
	 * number division.
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
				|| funName.equals("bvadd") || funName.equals("bvsub") || funName.equals("bvmul")
				|| funName.equals("div") || funName.equals("mod"));
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
		// This method is called for every subformula for which we let the
		// TermTransformer descend to subformulas.
		// Here, the arguments are the result of the "recursive" calls for the
		// subformulas.
		assert (isPolynomialFunctionSymbol(
				appTerm.getFunction().getName())) : "We only descended for polynomial functions";
		// First, we check if some of this arguments is the auxiliary error term.
		// If this is the case, we report that input is not polynomial.
		final IPolynomialTerm[] polynomialArgs = castAndCheckForNonPolynomialArguments(newArgs);
		if (polynomialArgs == null) {
			inputIsNotPolynomial();
			return;
		}
		final String funName = appTerm.getFunction().getName();
		final IPolynomialTerm result = convertArgumentsToFunction(polynomialArgs, funName);
		castAndSetResult(result);
	}

	/**
	 * Create an IPolynomialTerm out of the polynomialArgs, according to the given
	 * funName, if possible.
	 */
	private IPolynomialTerm convertArgumentsToFunction(final IPolynomialTerm[] polynomialArgs, final String funName) {
		switch (funName) {
		case "*":
			return multiply(polynomialArgs);

		case "bvmul":
			return multiply(polynomialArgs);

		case "+":
			return add(polynomialArgs);

		case "bvadd":
			return add(polynomialArgs);

		case "-":
			if (polynomialArgs.length == 1) {
				// unary minus
				return negate(polynomialArgs[0]);
			} else {
				return subtract(polynomialArgs);
			}

		case "bvsub":
			if (polynomialArgs.length == 1) {
				// unary minus
				return negate(polynomialArgs[0]);
			} else {
				return subtract(polynomialArgs);
			}

		case "div":
		case "/":
			if (polynomialArgs.length == 0) {
				throw new AssertionError("Division needs at least one argument");
			}
			return polynomialArgs[0].div(mScript, Arrays.copyOfRange(polynomialArgs, 1, polynomialArgs.length));
		case "mod":
			if (polynomialArgs.length > 2) {
				throw new AssertionError("Modulo needs exactly two arguments");
			}
			return polynomialArgs[0].mod(mScript, polynomialArgs[1]);
		default:
			throw new UnsupportedOperationException("unsupported symbol " + funName);
		}
	}

	/**
	 * Cast the interface IPolynomialTerm in a way that the TermTransformer accepts
	 * the result for "setResult". Execute "setResult" afterwards.
	 */
	private void castAndSetResult(final IPolynomialTerm poly) {
		if (poly instanceof PolynomialTerm) {
			setResult((PolynomialTerm) poly);
			return;
		} else if (poly instanceof AffineTerm) {
			setResult((AffineTerm) poly);
			return;
		}
		throw new UnsupportedOperationException("This IPolynomialTerm is instance of no known class.");
	}

	/**
	 * Multiply an array of PolynomialTerms.
	 */
	private static IPolynomialTerm multiply(final IPolynomialTerm[] polynomialArgs) {
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
		if (productWillBePolynomial(poly1, poly2)) {
			return PolynomialTerm.mulPolynomials(poly1, poly2);
		} else {
			return AffineTerm.mulAffineTerms(poly1, poly2);
		}
	}

	/**
	 * Determines whether the product of two polynomialTerms will most likely be
	 * truly polynomial (not affine). (It can still happen, that the result is
	 * affine, but we can't say that at this point in the code. The
	 * PolynomialTerm-class should return an AffineTerm if that's the case. Why not
	 * use PolynomialTerm everytime, then? Because of efficiency-reasons.) If the
	 * result is truly polynomial it returns true, false otherwise.
	 */
	private static boolean productWillBePolynomial(final IPolynomialTerm poly1, final IPolynomialTerm poly2) {
		return !poly1.isAffine() || !poly2.isAffine() || (!poly1.isConstant() && !poly2.isConstant());
	}

	/**
	 * Construct a {@link PolynomialTerm} that is the sum of all inputs.
	 */
	private static IPolynomialTerm add(final IPolynomialTerm[] polynomialArgs) {
		if (someTermIsPolynomial(polynomialArgs)) {
			return PolynomialTerm.sum(polynomialArgs);
		} else {
			return AffineTerm.sum(polynomialArgs);
		}
	}

	/**
	 * Returns true when one of the given Terms is truly polynomial (not
	 * representable by an AffineTerm).
	 */
	private static boolean someTermIsPolynomial(final IPolynomialTerm[] polynomialTerms) {
		for (final IPolynomialTerm polynomialTerm : polynomialTerms) {
			if (!polynomialTerm.isAffine()) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Construct negation (unary minus).
	 */
	private static IPolynomialTerm negate(final IPolynomialTerm polynomialTerm) {
		if (polynomialTerm.isAffine()) {
			return AffineTerm.mul(polynomialTerm, Rational.MONE);
		}
		return PolynomialTerm.mul(polynomialTerm, Rational.MONE);
	}

	/**
	 * Given {@link PolynomialTerm}s <code>t1,t2,...,tn</code> construct an
	 * {@link PolynomialTerm} that represents the difference
	 * <code>t1-t2-...-tn</code>, i.e., the {@link PolynomialTerm} that is
	 * equivalent to <code>t1-(t2+...+tn)</code>
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
	 * Convert an array of {@link Term}s into an an array of {@link PolynomialTerm}s
	 * by casting every single element. In case an element of the input is our
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

	/**
	 * Convert SMT {@link Term} into an {@link IPolynomialTerm}. We return null if
	 * we the {@link Term} cannot be converted into an {@link IPolynomialTerm},
	 * e.g., because its sort is Bool.
	 */
	public static IPolynomialTerm convert(final Script script, final Term term) {
		final IPolynomialTerm result;
		if (!hasSupportedSort(term)) {
			result = null;
		} else {
			result = (IPolynomialTerm) new PolynomialTermTransformer(script).transform(term);
			if (result.isErrorTerm()) {
				throw new UnsupportedOperationException("Unknown conversion problem: " + term);
			}
		}
		return result;
	}

	/**
	 * Helper class that rewrites terms of the form (* (div t1 t2) t2) to the form (- t1 (mod t1 t2)).
	 *
	 * The idea is that the latter form is more useful on polynomial relations, as an occurrence of t1 on the other side
	 * of the relation can be eliminated along with the first occurrence in (- t1 (mod t1 t2)).
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 */
	private static class MulDivModRewriter implements Walker {
		private final Term mNumerator;
		private final Term mDivisorFactor;

		private MulDivModRewriter(final Term numerator, final Term divisorFactor) {
			mNumerator = numerator;
			mDivisorFactor = divisorFactor;
		}

		public void run(final PolynomialTermTransformer engine) {
			engine.enqueueWalker(this);
			engine.pushTerm(mDivisorFactor);
			engine.pushTerm(mNumerator);

		}

		@Override
		public void walk(final NonRecursive engine) {
			final PolynomialTermTransformer transformer = (PolynomialTermTransformer) engine;
			final Term[] oldArgs = new Term[] { mNumerator, mDivisorFactor };
			final Term[] newArgs = transformer.getConverted(oldArgs);
			final IPolynomialTerm[] polynomialArgs = castAndCheckForNonPolynomialArguments(newArgs);
			if (polynomialArgs == null) {
				transformer.inputIsNotPolynomial();
				return;
			}

			final var result = subtract(new IPolynomialTerm[] { polynomialArgs[0],
					polynomialArgs[0].mod(transformer.mScript, polynomialArgs[1]) });
			transformer.castAndSetResult(result);
		}

		/**
		 * Determines if the given term has the form (* (div t1 t2) t2), and if so, creates a {@link MulDivModRewriter}
		 * instance for rewriting the given term into (- t1 (mod t1 t2)).
		 *
		 * @param term
		 * @return a suitable instance, or {@code null} if the given term does not have the required form
		 */
		public static MulDivModRewriter forTerm(final Term term) {
			if (!(term instanceof ApplicationTerm)) {
				return null;
			}
			final var appTerm = (ApplicationTerm) term;
			if (!appTerm.getFunction().getName().equals("*") || appTerm.getParameters().length != 2) {
				// TODO should we add support for more than 2 parameters?
				return null;
			}
			final var params = appTerm.getParameters();
			final var result = forTerms(params[0], params[1]);
			if (result == null) {
				return forTerms(params[1], params[0]);
			}
			return result;
		}

		private static MulDivModRewriter forTerms(final Term div, final Term other) {
			if (!(div instanceof ApplicationTerm)) {
				return null;
			}
			final var appTerm = (ApplicationTerm) div;
			if (!appTerm.getFunction().getName().equals("div") || appTerm.getParameters().length != 2) {
				// TODO should we add support for more than 2 parameters?
				return null;
			}
			final var params = appTerm.getParameters();
			if (params[1].equals(other)) {
				return new MulDivModRewriter(params[0], other);
			}
			return null;
		}
	}
}
