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

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
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
 * Transform a Term into an AffineTerm. Result is an auxiliary error term if the
 * input was not affine.
 * 
 * @author Matthias Heizmann
 * 
 */
public class AffineTermTransformer extends TermTransformer {
	private final Script mScript;

	public AffineTermTransformer(final Script script) {
		mScript = script;
	}

	@Override
	protected void convert(final Term term) {
		if (term instanceof TermVariable) {
			final TermVariable tv = (TermVariable) term;
			if (tv.getSort().isNumericSort() || SmtSortUtils.isBitvecSort(tv.getSort())) {
				final AffineTerm result = new AffineTerm(tv);
				setResult(result);
				return;
			}
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final String funName = appTerm.getFunction().getName();
			if (BitvectorUtils.isBitvectorConstant(appTerm.getFunction())) {
				final BitvectorConstant bv = BitvectorUtils.constructBitvectorConstant(appTerm);
				final Rational rational = Rational.valueOf(bv.getValue(), BigInteger.ONE);
				final AffineTerm result = new AffineTerm(appTerm.getSort(), rational);
				setResult(result);
				return;
			}
			if (isAffineSymbol(funName)) {
				super.convert(term);
				return;
			} else if (term.getSort().isNumericSort() || SmtSortUtils.isBitvecSort(term.getSort())) {
				final AffineTerm result = new AffineTerm(appTerm);
				setResult(result);
				return;
			} else {
				resultIsNotAffine();
				return;
			}
//			} else if (funName.equals("to_real")) {
//				final AffineTerm result = convertToReal(appTerm);
//				setResult(result);
//				return;
//			} else if (funName.equals("select")) {
//				final AffineTerm result = new AffineTerm(appTerm);
//				setResult(result);
//				return;
//			} else if (funName.equals("mod")) {
//				final AffineTerm result;
//				final Term simplified = SmtUtils.termWithLocalSimplification(
//						mScript, "mod", appTerm.getSort().getIndices(), appTerm.getParameters());
//				if (simplified instanceof ApplicationTerm) {
//					result = new AffineTerm((ApplicationTerm) simplified);
//				} else if (simplified instanceof ConstantTerm) {
//					result = new AffineTerm(simplified.getSort(), 
//							SmtUtils.convertConstantTermToRational((ConstantTerm) simplified));
//				} else {
//					throw new AssertionError(
//							"should be either ApplicationTerm or ConstantTerm " + simplified);
//				}
//				setResult(result);
//				return;
//			} else if (appTerm.getParameters().length == 0 && appTerm.getSort().isNumericSort()) {
//				// appTerm is a constant (0-ary function)
//				final AffineTerm result = new AffineTerm(appTerm);
//				setResult(result);
//				return;
//			} else {
//				resultIsNotAffine();
//				return;
//			}
		} else if (term instanceof ConstantTerm) {
			final ConstantTerm constTerm = (ConstantTerm) term;
			if (constTerm.getSort().isNumericSort()) {
				final AffineTerm result = convertConstantNumericTerm(constTerm);
				setResult(result);
				return;
			} else {
				final AffineTerm errorTerm = new AffineTerm(); 
				setResult(errorTerm);
				return;
			}
		}
		super.convert(term);
	}

	/**
	 * Convert ConstantTerm with numericSort to AffineTerm
	 * 
	 */
	private AffineTerm convertConstantNumericTerm(final ConstantTerm constTerm) {
		final Rational rational = SmtUtils.convertConstantTermToRational(constTerm);
		final AffineTerm result = new AffineTerm(constTerm.getSort(), rational);
		return result;
	}

	/**
	 * Convert input term of the form "to_real(param)" to affine term.
	 * If the input term is an integer literal we convert it to a real literal,
	 * otherwise we consider the "to_real" term as a variable of an affine term.
	 */
	private AffineTerm convertToReal(final ApplicationTerm term) {
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
			} else {
				final AffineTerm intTerm = convertConstantNumericTerm(constant);
				final AffineTerm realTerm = new AffineTerm(term.getSort(), intTerm.getConstant());
				result = realTerm;
			}
		} else {
			result = new AffineTerm(term);
		}
		return result;
	}

	private boolean isAffineSymbol(final String funName) {
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
					resultIsNotAffine();
					return;
				}
			} else {
				resultIsNotAffine();
				return;
			}
		}

		// if (!appTerm.getSort().isNumericSort()) {
		// resultIsNotAffine();
		// return;
		// }
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
						resultIsNotAffine();
						return;
					}
				}
			}
			AffineTerm result;
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
					resultIsNotAffine();
					return;
				}
			}
			final Sort sort = appTerm.getSort();
			AffineTerm result;
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
	 * set result to auxiliary error term
	 */
	private void resultIsNotAffine() {
		setResult(new AffineTerm());
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

}
