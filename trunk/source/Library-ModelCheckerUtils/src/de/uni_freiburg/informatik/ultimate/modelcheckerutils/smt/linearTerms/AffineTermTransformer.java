package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms;

import java.math.BigDecimal;
import java.math.BigInteger;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;

/**
 * Transform a Term into an AffineTerm. 
 * Result is an auxiliary error term if the input was not affine.
 * 
 * @author Matthias Heizman
 *
 */
public class AffineTermTransformer extends TermTransformer {
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(ModelCheckerUtils.sPluginID);
	
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
			} else {
				AffineTerm result = new AffineTerm(appTerm);
				setResult(result);
				return;
			}
		} else if (term instanceof ConstantTerm) {
			ConstantTerm constTerm = (ConstantTerm) term;
			if (constTerm.getSort().isNumericSort()) {
				AffineTerm result = convertConstantNumericTerm(constTerm);
				setResult(result);
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
		assert constTerm.getSort().isNumericSort();
		Object value = constTerm.getValue();
		Rational rational;
		if (constTerm.getSort().getName().equals("Int")) {
			if (value instanceof BigInteger) {
				rational = Rational.valueOf((BigInteger) value, BigInteger.ONE);
			} else if (value instanceof Rational) {
				rational = (Rational) value;
			} else {
				throw new UnsupportedOperationException();
			}
		} else  if (constTerm.getSort().getName().equals("Real")) {
			if (value instanceof BigDecimal) {
				rational = decimalToRational((BigDecimal) value);
			} else if (value instanceof Rational) {
				rational = (Rational) value;
			} else {
				throw new UnsupportedOperationException();
			}
		} 
		else {
			throw new UnsupportedOperationException();
		}
		AffineTerm result = new AffineTerm(constTerm.getSort(), rational);
		return result;
	}

	/**
	 * Convert tem of the form "to_real(param)" to affine term.
	 * At the moment we support only the case where param in an integer literal
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
		return (funName.equals("+") || funName.equals("-") || 
				funName.equals("*") || funName.equals("/"));
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		AffineTerm[] affineArgs = new AffineTerm[newArgs.length];
		for (int i = 0; i<affineArgs.length; i++) {
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
		
//		if (!appTerm.getSort().isNumericSort()) {
//			resultIsNotAffine();
//			return;
//		}
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
//				assert affineArg.getSort() == sort;
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
				//unary minus
				AffineTerm param = affineArgs[0];
				result = new AffineTerm(param, Rational.MONE);
			} else {
				AffineTerm[] resAffineArgs = new AffineTerm[affineArgs.length];
				resAffineArgs[0] = affineArgs[0];
				for (int i = 1; i<resAffineArgs.length; i++) {
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
			for (int i=1; i<affineArgs.length; i++) {
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
		s_Logger.debug("not affine");
		setResult(new AffineTerm());
	}
	
	
	/**
	 * Convert a BigDecimal into a Rational.
	 * Stolen from Jochen's code
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
