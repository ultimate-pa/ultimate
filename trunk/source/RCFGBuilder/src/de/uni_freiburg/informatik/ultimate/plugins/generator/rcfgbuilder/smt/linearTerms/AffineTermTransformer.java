package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.linearTerms;

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
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;

/**
 * Transform Term into AffineTerm.
 * @author Matthias Heizman
 *
 */
public class AffineTermTransformer extends TermTransformer {
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	@Override
	protected void convert(Term term) {
		if (term instanceof TermVariable) {
			TermVariable tv = (TermVariable) term;
			AffineTerm result = new AffineTerm(tv);
			setResult(result);
			return;
		} else if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			String funName = appTerm.getFunction().getName();
			if (funName.equals("select")) {
				AffineTerm result = new AffineTerm(appTerm);
				setResult(result);
				return;
			}
		} else if (term instanceof ConstantTerm) {
			ConstantTerm constTerm = (ConstantTerm) term;
			if (constTerm.getSort().isNumericSort()) {
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
				setResult(result);
				return;
			}
		}
		super.convert(term);
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		if (!appTerm.getSort().isNumericSort()) {
			resultIsNotAffine();
			return;
		}
		String funName = appTerm.getFunction().getName();
		if (funName.equals("*")) {
			AffineTerm affineTerm = null;
			Rational multiplier = Rational.ONE;
			Sort sort = appTerm.getSort();
			for (Term termArg : newArgs) {
				if (!(termArg instanceof AffineTerm)) {
					resultIsNotAffine();
					return;
				}
				AffineTerm affineArg = (AffineTerm) termArg;
				assert affineArg.getSort() == sort;
				if (affineArg.isConstant()) {
					multiplier = multiplier.mul(affineTerm.getConstant());
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
			AffineTerm[] affineArgs = new AffineTerm[newArgs.length];
			for (int i = 0; i<affineArgs.length; i++) {
				affineArgs[i] = (AffineTerm) newArgs[i];
			}
			AffineTerm result = new AffineTerm(affineArgs);
			setResult(result);
			return;
		} else if (funName.equals("-")) {
			AffineTerm result;
			if (newArgs.length == 1) {
				//unary minus
				AffineTerm param = (AffineTerm) newArgs[0];
				result = new AffineTerm(param, Rational.MONE);
			} else {
				AffineTerm[] affineArgs = new AffineTerm[newArgs.length];
				affineArgs[0] = (AffineTerm) newArgs[0];
				for (int i = 1; i<affineArgs.length; i++) {
					affineArgs[i] = new AffineTerm((AffineTerm) newArgs[i], Rational.MONE);
				}
				result = new AffineTerm(affineArgs);
			}
			setResult(result);
			return;
		} else {
			throw new UnsupportedOperationException("unknown symbol " + funName);
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
