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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms;

import java.math.BigDecimal;
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
			final AffineTerm result = new AffineTerm(term.getSort(), valueOfLiteral);
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
			final AffineTerm result = new AffineTerm(term);
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
	 * Check if term represents a literal. If this is the case, then return
	 * its value as a {@link Rational} otherwisereturn true.
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
	 * represents an "affine function". We call a function an "affine function"
	 * if it implements an addition, subtraction, or multiplication.
	 * TODO 2019-02-28 Matthias: It seems that currently, we allow also division
	 * or reals but I have some doubts that this is desired.
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
		final AffineTerm[] affineArgs = new AffineTerm[newArgs.length];
		for (int i = 0; i < affineArgs.length; i++) {
			if (newArgs[i] instanceof AffineTerm) {
				affineArgs[i] = (AffineTerm) newArgs[i];
				if (affineArgs[i].isErrorTerm()) {
					inputIsNotAffine();
					return;
				}
			} else {
				inputIsNotAffine();
				return;
			}
		}

		if (appTerm.getParameters().length == 0) {
			final AffineTerm result = new AffineTerm(appTerm);
			setResult(result);
			return;
		}
		final String funName = appTerm.getFunction().getName();
		if (funName.equals("*") || funName.equals("bvmul")) {
			// the result is the product of at most one affineTerm and one
			// multiplier (that may be obtained from a product of constants)
			AffineTerm affineTerm = null;
			Rational multiplier = Rational.ONE;
			final Sort sort = appTerm.getSort();
			for (final Term termArg : affineArgs) {
				final AffineTerm affineArg = (AffineTerm) termArg;
				// assert affineArg.getSort() == sort;
				if (affineArg.isConstant()) {
					multiplier = multiplier.mul(affineArg.getConstant());
				} else {
					if (affineTerm == null) {
						affineTerm = affineArg;
					} else {
						inputIsNotAffine();
						return;
					}
				}
			}
			final AffineTerm result;
			if (affineTerm == null) {
				result = new AffineTerm(sort, multiplier);
			} else {
				result = new AffineTerm(affineTerm, multiplier);
			}
			setResult(result);
			return;
		} else if (funName.equals("+") || funName.equals("bvadd")) {
			final AffineTerm result = new AffineTerm(affineArgs);
			setResult(result);
			return;
		} else if (funName.equals("-") || funName.equals("bvsub")) {
			AffineTerm result;
			if (affineArgs.length == 1) {
				// unary minus
				final AffineTerm param = affineArgs[0];
				result = new AffineTerm(param, Rational.MONE);
			} else {
				final AffineTerm[] resAffineArgs = new AffineTerm[affineArgs.length];
				resAffineArgs[0] = affineArgs[0];
				for (int i = 1; i < resAffineArgs.length; i++) {
					resAffineArgs[i] = new AffineTerm(affineArgs[i], Rational.MONE);
				}
				result = new AffineTerm(resAffineArgs);
			}
			setResult(result);
			return;
		} else if (funName.equals("/")) {
			// the result is the product of at most one affineTerm and one
			// multiplier (that may be obtained from a division of constants)
			final AffineTerm affineTerm;
			Rational multiplier;
			if (affineArgs[0].isConstant()) {
				affineTerm = null;
				multiplier = affineArgs[0].getConstant();
			} else {
				affineTerm = affineArgs[0];
				multiplier = Rational.ONE;
			}
			for (int i = 1; i < affineArgs.length; i++) {
				if (affineArgs[i].isConstant()) {
					multiplier = multiplier.mul(affineArgs[i].getConstant().inverse());
				} else {
					// unsupported terms in divisor
					inputIsNotAffine();
					return;
				}
			}
			final Sort sort = appTerm.getSort();
			final AffineTerm result;
			if (affineTerm == null) {
				result = new AffineTerm(sort, multiplier);
			} else {
				result = new AffineTerm(affineTerm, multiplier);
			}
			setResult(result);
			return;
		} else {
			throw new UnsupportedOperationException("unsupported symbol " + funName);
		}
	}



	/**
	 * Convert a BigDecimal into a Rational. Stolen from Jochen's code
	 * de.uni_freiburg.informatik.ultimate.smtinterpol.convert.ConvertFormula.
	 */
	public static Rational decimalToRational(final BigDecimal d) {
		Rational rat;
		if (d.scale() <= 0) {
			final BigInteger num = d.toBigInteger();
			rat = Rational.valueOf(num, BigInteger.ONE);
		} else {
			final BigInteger num = d.unscaledValue();
			final BigInteger denom = BigInteger.TEN.pow(d.scale());
			rat = Rational.valueOf(num, denom);
		}
		return rat;
	}



	///////////////////////////////////////////////////////////////////////////////////////////////////////////////
	// Unused auxiliary methods that we may use in the future.

	/**
	 * Convert ConstantTerm with numericSort to AffineTerm
	 *
	 */
	private static AffineTerm convertConstantNumericTerm(final ConstantTerm constTerm) {
		final Rational rational = SmtUtils.convertConstantTermToRational(constTerm);
		final AffineTerm result = new AffineTerm(constTerm.getSort(), rational);
		return result;
	}

	/**
	 * Convert input term of the form "to_real(param)" to affine term. If the input term is an integer literal we
	 * convert it to a real literal, otherwise we consider the "to_real" term as a variable of an affine term.
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
			final AffineTerm realTerm = new AffineTerm(term.getSort(), intTerm.getConstant());
			result = realTerm;
		} else {
			result = new AffineTerm(term);
		}
		return result;
	}

}
