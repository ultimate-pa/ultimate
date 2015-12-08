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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms;

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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;

/**
 * Transform a Term into an AffineTerm. Result is an auxiliary error term if the
 * input was not affine.
 * 
 * @author Matthias Heizmann
 * 
 */
public class AffineTermTransformer extends TermTransformer {
	private final Script m_Script;

	public AffineTermTransformer(Script script) {
		m_Script = script;
	}

	@Override
	protected void convert(Term term) {
		if (term instanceof TermVariable) {
			TermVariable tv = (TermVariable) term;
			if (tv.getSort().isNumericSort()) {
				AffineTerm result = new AffineTerm(tv);
				setResult(result);
				return;
			}
		} else if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			String funName = appTerm.getFunction().getName();
			if (isAffineSymbol(funName)) {
				super.convert(term);
				return;
			} else if (funName.equals("to_real")) {
				AffineTerm result = convertToReal(appTerm);
				setResult(result);
				return;
			} else if (funName.equals("select")) {
				AffineTerm result = new AffineTerm(appTerm);
				setResult(result);
				return;
			} else if (funName.equals("mod")) {
				final AffineTerm result;
				Term simplified = SmtUtils.termWithLocalSimplification(
						m_Script, "mod", appTerm.getSort().getIndices(), appTerm.getParameters());
				if (simplified instanceof ApplicationTerm) {
					result = new AffineTerm((ApplicationTerm) simplified);
				} else if (simplified instanceof ConstantTerm) {
					result = new AffineTerm(simplified.getSort(), 
							SmtUtils.convertConstantTermToRational((ConstantTerm) simplified));
				} else {
					throw new AssertionError(
							"should be either ApplicationTerm or ConstantTerm " + simplified);
				}
				setResult(result);
				return;
			} else if (appTerm.getParameters().length == 0 && appTerm.getSort().isNumericSort()) {
				// appTerm is a constant (0-ary function)
				AffineTerm result = new AffineTerm(appTerm);
				setResult(result);
				return;
			} else {
				resultIsNotAffine();
				return;
			}
		} else if (term instanceof ConstantTerm) {
			ConstantTerm constTerm = (ConstantTerm) term;
			if (constTerm.getSort().isNumericSort()) {
				AffineTerm result = convertConstantNumericTerm(constTerm);
				setResult(result);
				return;
			} else {
				AffineTerm errorTerm = new AffineTerm(); 
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
	private AffineTerm convertConstantNumericTerm(ConstantTerm constTerm) {
		Rational rational = SmtUtils.convertConstantTermToRational(constTerm);
		AffineTerm result = new AffineTerm(constTerm.getSort(), rational);
		return result;
	}

	/**
	 * Convert tem of the form "to_real(param)" to affine term. At the moment we
	 * support only the case where param in an integer literal
	 * 
	 * @param term
	 * @return
	 */
	private AffineTerm convertToReal(ApplicationTerm term) {
		if (!term.getFunction().getName().equals("to_real")) {
			throw new IllegalArgumentException("no to_real term");
		}
		Term[] params = ((ApplicationTerm) term).getParameters();
		if (params.length > 1) {
			throw new UnsupportedOperationException();
		}
		Term param = params[0];
		if (param instanceof ConstantTerm) {
			ConstantTerm constant = (ConstantTerm) param;
			if (!constant.getSort().getName().equals("Int")) {
				throw new UnsupportedOperationException();
			} else {
				AffineTerm intTerm = convertConstantNumericTerm(constant);
				AffineTerm realTerm = new AffineTerm(term.getSort(), intTerm.getConstant());
				return realTerm;
			}
		} else {
			throw new UnsupportedOperationException();
		}
	}

	private boolean isAffineSymbol(String funName) {
		return (funName.equals("+") || funName.equals("-") || funName.equals("*") || funName.equals("/"));
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		AffineTerm[] affineArgs = new AffineTerm[newArgs.length];
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
			AffineTerm result = new AffineTerm(appTerm);
			setResult(result);
			return;
		}
		String funName = appTerm.getFunction().getName();
		if (funName.equals("*")) {
			// the result is the product of at most one affineTerm and one
			// multiplier (that may be obtained from a product of constants)
			AffineTerm affineTerm = null;
			Rational multiplier = Rational.ONE;
			Sort sort = appTerm.getSort();
			for (Term termArg : affineArgs) {
				AffineTerm affineArg = (AffineTerm) termArg;
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
		} else if (funName.equals("+")) {
			AffineTerm result = new AffineTerm(affineArgs);
			setResult(result);
			return;
		} else if (funName.equals("-")) {
			AffineTerm result;
			if (affineArgs.length == 1) {
				// unary minus
				AffineTerm param = affineArgs[0];
				result = new AffineTerm(param, Rational.MONE);
			} else {
				AffineTerm[] resAffineArgs = new AffineTerm[affineArgs.length];
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
			Sort sort = appTerm.getSort();
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
	public static Rational decimalToRational(BigDecimal d) {
		Rational rat;
		if (d.scale() <= 0) {
			BigInteger num = d.toBigInteger();
			rat = Rational.valueOf(num, BigInteger.ONE);
		} else {
			BigInteger num = d.unscaledValue();
			BigInteger denom = BigInteger.TEN.pow(d.scale());
			rat = Rational.valueOf(num, denom);
		}
		return rat;
	}

}
