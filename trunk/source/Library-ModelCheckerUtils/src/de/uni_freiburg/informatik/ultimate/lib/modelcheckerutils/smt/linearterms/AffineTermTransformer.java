/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms;

import java.math.BigInteger;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.BitvectorUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant;

/**
 * Transforms a {@link Term} which is "affine" into our {@link AffineTerm} data
 * structure. The result is an auxiliary error term if the input was not affine.
 *
 * The transformation is done by an recursive algorithm. However, in order to
 * circumvent the problem that the performance of Java virtual machines is
 * rather poor for recursive methods calls we implement the algorithm by using
 * our {@link TermTransformer}. The {@link TermTransformer} allows us to
 * implement recursive algorithms for {@link Term}s without recursive methods
 * calls by explicitly using a stack.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class AffineTermTransformer extends TermTransformer {
	private final Script mScript;
	/**
	 * Predicate that defines which Terms might be variables of the
	 * {@link AffineTerm}. Currently, every {@link TermVariable} and every
	 * {@link ApplicationTerm} can be a variable of the result. In
	 * the future this may become a parameter in order to allow users
	 * of this class to be more restrictive.
	 */
	private final Predicate<Term> mIsAffineVariable = (x -> ((x instanceof TermVariable)
			|| (x instanceof ApplicationTerm)));

	public AffineTermTransformer(final Script script) {
		mScript = script;
	}

	@Override
	protected void convert(final Term term) {
		// If the term has a sort that is not supported, we report
		// that the input cannot be converted into an AffineTerm.
		// This is implemented by returning an special kind
		// of AffineTerm.
		if (!hasSupportedSort(term)) {
			inputIsNotAffine();
			return;
		}
		// Otherwise, if the terms represents a literal, we convert the literal
		// to an AffineTerm and tell the TermTransformer that this
		// is the result (i.e., it should not descend to subformulas).
		final Rational valueOfLiteral = tryToConvertToLiteral(mScript, term);
		if (valueOfLiteral != null) {
			final AffineTerm result = AffineTerm.constructConstant(term.getSort(), valueOfLiteral);
			setResult(result);
			return;
		}
		// Otherwise, if the term represents an "affine function" we tell
		// TermTransformer to descend to subformulas.
		if (isAffineFunction(term)) {
			super.convert(term);
			return;
		}
		// Otherwise, the term is considered as a variable of our AffineTerms,
		// we construct an AffineTerm that represents a variable and tell the
		// TermTransformer that this
		// is the result (i.e., it should not descend to subformulas).
		if (mIsAffineVariable.test(term)) {
			final AffineTerm result = AffineTerm.constructVariable(term);
			setResult(result);
			return;
		}
		// Otherwise, the input cannot be converted to an AffineTerm.
		inputIsNotAffine();
		return;
	}

	/**
	 * Sets result to auxiliary error term.
	 */
	private void inputIsNotAffine() {
		setResult(new AffineTerm());
	}

	/**
	 * Currently, we support the SMT {@link Sort}s Int and Real (called numeric
	 * sorts) and the bitvector sorts.
	 */
	private static boolean hasSupportedSort(final Term term) {
		return SmtSortUtils.isNumericSort(term.getSort()) || SmtSortUtils.isBitvecSort(term.getSort());
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

	/**
	 * Check if term is an {@link ApplicationTerm} whose {@link FunctionSymbol}
	 * represents an "affine function". We call a function an "affine function" if
	 * it implements an addition, subtraction, multiplication, or real number
	 * division.
	 */
	private static boolean isAffineFunction(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			return isAffineFunctionSymbol(appTerm.getFunction().getName());
		} else {
			return false;
		}
	}

	private static boolean isAffineFunctionSymbol(final String funName) {
		return (funName.equals("+") || funName.equals("-") || funName.equals("*") || funName.equals("/")
				|| funName.equals("bvadd") || funName.equals("bvsub") || funName.equals("bvmul"));
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
		// This method is called for every subformula for which we let the
		// TermTransformer descend to subformulas.
		// Here, the arguments are the result of the "recursive" calls for the
		// subformulas.
		assert (isAffineFunctionSymbol(appTerm.getFunction().getName())) : "We only descended for affine functions";
		// First, we check if some of this arguments is the auxiliary error term.
		// If this is the case, we report that input is not affine.
		final AffineTerm[] affineArgs = castAndCheckForNonAffineArguments(newArgs);
		if (affineArgs == null) {
			inputIsNotAffine();
			return;
		}
		final String funName = appTerm.getFunction().getName();
		if (funName.equals("*") || funName.equals("bvmul")) {
			final Sort sort = appTerm.getSort();
			final AffineTerm result = tryToMultiply(sort, affineArgs);
			if (result == null) {
				inputIsNotAffine();
				return;
			}
			setResult(result);
			return;
		} else if (funName.equals("+") || funName.equals("bvadd")) {
			final AffineTerm result = add(affineArgs);
			setResult(result);
			return;
		} else if (funName.equals("-") || funName.equals("bvsub")) {
			final AffineTerm result;
			if (affineArgs.length == 1) {
				// unary minus
				result = negate(affineArgs[0]);
			} else {
				result = subtract(affineArgs);
			}
			setResult(result);
			return;
		} else if (funName.equals("/")) {
			final Sort sort = appTerm.getSort();
			final AffineTerm result = divide(sort, affineArgs);
			if (result == null) {
				inputIsNotAffine();
				return;
			}
			setResult(result);
			return;
		} else {
			throw new UnsupportedOperationException("unsupported symbol " + funName);
		}
	}

	/**
	 * Convert an array of {@link Term}s into an an array of {@link AffineTerm}s by
	 * casting every single element. In case an element of the input is our
	 * auxiliary error term we return null instead.
	 */
	private static AffineTerm[] castAndCheckForNonAffineArguments(final Term[] terms) {
		final AffineTerm[] affineTerms = new AffineTerm[terms.length];
		for (int i = 0; i < affineTerms.length; i++) {
			if (terms[i] instanceof AffineTerm) {
				affineTerms[i] = (AffineTerm) terms[i];
				if (affineTerms[i].isErrorTerm()) {
					return null;
				}
			} else {
				throw new AssertionError();
			}
		}
		return affineTerms;
	}

	/**
	 * Construct an {@link AffineTerm} that is the sum of all inputs.
	 */
	private static AffineTerm add(final AffineTerm[] affineArgs) {
		final AffineTerm result = AffineTerm.sum(affineArgs);
		return result;
	}

	/**
	 * Construct negation (unary minus).
	 */
	private static AffineTerm negate(final AffineTerm affineTerm) {
		return AffineTerm.mul(affineTerm, Rational.MONE);
	}

	/**
	 * Given {@link AffineTerm}s <code>t1,t2,...,tn</code> construct an
	 * {@link AffineTerm} that represents the difference <code>t1-t2-...-tn</code>,
	 * i.e., the {@link AffineTerm} that is equivalent to
	 * <code>t1-(t2+...+tn)</code>
	 */
	private static AffineTerm subtract(final AffineTerm[] input) {
		assert input.length > 1;
		final AffineTerm[] argumentsForSum = new AffineTerm[input.length];
		// negate all arguments but the first (at position 0)
		argumentsForSum[0] = input[0];
		for (int i = 1; i < argumentsForSum.length; i++) {
			argumentsForSum[i] = AffineTerm.mul(input[i], Rational.MONE);
		}
		// construct the sum
		return add(argumentsForSum);
	}

	/**
	 * Multiply an array of AffineTerms. If more that one argument is not a literal
	 * the result is not affine and we return null.
	 */
	private static AffineTerm tryToMultiply(final Sort sort, final AffineTerm[] affineTerms) {
		AffineTerm result;
		AffineTerm nonLiteralArgument = null;
		Rational multiplier = Rational.ONE;
		for (final AffineTerm affineTerm : affineTerms) {
			if (affineTerm.isConstant()) {
				multiplier = multiplier.mul(affineTerm.getConstant());
			} else {
				if (nonLiteralArgument == null) {
					nonLiteralArgument = affineTerm;
				} else {
					// we have at least two arguments that are not literals
					return null;
				}
			}
		}
		if (nonLiteralArgument == null) {
			result = AffineTerm.constructConstant(sort, multiplier);
		} else {
			result = AffineTerm.mul(nonLiteralArgument, multiplier);
		}
		return result;
	}

	/**
	 * Given {@link AffineTerm}s <code>t1,t2,...,tn</code> construct an
	 * {@link AffineTerm} that represents the quotient <code>t1/t2/.../tn</code>,
	 * i.e., the {@link AffineTerm} that is equivalent to
	 * <code>t1*((1/t2)+...+(1/tn))</code>. Note that the function "/" is only
	 * defined the sort of reals. For integer division we have the function "div"
	 * which is currently not supported by our affine terms.
	 */
	private static AffineTerm divide(final Sort sort, final AffineTerm[] affineArgs) {
		assert SmtSortUtils.isRealSort(sort);
		final AffineTerm affineTerm;
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
				return null;
			}
		}
		if (affineTerm == null) {
			result = AffineTerm.constructConstant(sort, multiplier);
		} else {
			result = AffineTerm.mul(affineTerm, multiplier);
		}
		return result;
	}




	///////////////////////////////////////////////////////////////////////////////////////////////////////////////
	// Unused auxiliary methods that we may use in the future.

	/**
	 * Convert ConstantTerm with numericSort to AffineTerm
	 *
	 */
	private static AffineTerm convertConstantNumericTerm(final ConstantTerm constTerm) {
		final Rational rational = SmtUtils.convertConstantTermToRational(constTerm);
		final AffineTerm result = AffineTerm.constructConstant(constTerm.getSort(), rational);
		return result;
	}

	/**
	 * Convert input term of the form "to_real(param)" to affine term. If the input
	 * term is an integer literal we convert it to a real literal, otherwise we
	 * consider the "to_real" term as a variable of an affine term.
	 */
	private static AffineTerm convertToReal(final ApplicationTerm term) {
		if (!term.getFunction().getName().equals("to_real")) {
			throw new IllegalArgumentException("no to_real term");
		}
		final Term[] params = term.getParameters();
		if (params.length > 1) {
			throw new UnsupportedOperationException();
		}
		final AffineTerm result;
		final Term param = params[0];
		if (param instanceof ConstantTerm) {
			final ConstantTerm constant = (ConstantTerm) param;
			if (!SmtSortUtils.isIntSort(constant.getSort())) {
				throw new UnsupportedOperationException();
			}
			final AffineTerm intTerm = convertConstantNumericTerm(constant);
			final AffineTerm realTerm = AffineTerm.constructConstant(term.getSort(), intTerm.getConstant());
			result = realTerm;
		} else {
			result = AffineTerm.constructVariable(term);
		}
		return result;
	}

}
