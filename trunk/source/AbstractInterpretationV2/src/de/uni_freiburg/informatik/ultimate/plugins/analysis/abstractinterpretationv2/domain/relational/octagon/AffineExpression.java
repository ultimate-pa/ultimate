package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.math.MathContext;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

public class AffineExpression {

	private Map<String, BigDecimal> mCoefficients;
	private BigDecimal mConstant;
	
	public AffineExpression(Map<String, BigDecimal> coefficients, BigDecimal constant) {
		mCoefficients = coefficients;
		mConstant = constant;
		removeZeroSummands();
	}

	private AffineExpression() {
		mCoefficients = new HashMap<>();
		mConstant = BigDecimal.ZERO;
	}
	
	private void removeZeroSummands() {
		Iterator<BigDecimal> iter = mCoefficients.values().iterator();
		while (iter.hasNext()) {
			if (iter.next().signum() == 0) { // "signum()" is faster than "comparTo(0)"
				iter.remove();
			}
		}
	}
	
	public BigDecimal getCoefficient(String var) {
		BigDecimal factor = mCoefficients.get(var);
		return (factor == null) ? BigDecimal.ZERO : factor;
	}
	
	public boolean isConstant() {
//		for (BigDecimal factor : mMapVarToCoefficient.values()) {
//			if (factor.signum() != 0) {
//				return false;
//			}
//		}
//		return true;
		return mCoefficients.isEmpty();
	}
	
	public AffineExpression add(AffineExpression summand) {
		AffineExpression sum = new AffineExpression();
		sum.mConstant = mConstant.add(summand.mConstant);
		Set<String> vars = new HashSet<>();
		vars.addAll(mCoefficients.keySet());
		vars.addAll(summand.mCoefficients.keySet());
		for (String v : vars) {
			BigDecimal sumFactor = getCoefficient(v).add(summand.getCoefficient(v));
			sum.mCoefficients.put(v, sumFactor);
		}
		sum.removeZeroSummands();
		return sum;
	}
	
	public AffineExpression negate() {
		AffineExpression negation = new AffineExpression();
		negation.mConstant = mConstant.negate();
		for (Map.Entry<String, BigDecimal> entry : mCoefficients.entrySet()) {
			negation.mCoefficients.put(entry.getKey(), entry.getValue().negate());
		}
		return negation;
	}
	
	public AffineExpression multiply(AffineExpression factor) {
		AffineExpression affineFactor, constantFactor;
		if (isConstant()) {
			affineFactor = factor;
			constantFactor = this;
		} else if (factor.isConstant()) {
			affineFactor = this;
			constantFactor = factor;
		} else {
			return null;
		}
		AffineExpression product = new AffineExpression();
		product.mConstant = affineFactor.mConstant.multiply(constantFactor.mConstant);
		for (Map.Entry<String, BigDecimal> entry : affineFactor.mCoefficients.entrySet()) {
			BigDecimal newCoefficent = entry.getValue().multiply(constantFactor.mConstant);
			product.mCoefficients.put(entry.getKey(), newCoefficent);
		}
		return product;
	}

	public AffineExpression divide(AffineExpression divisor) {
		if (!divisor.isConstant()) {
			if (divisor.equals(this)) {
				AffineExpression one = new AffineExpression();
				one.mConstant = BigDecimal.ONE;
				return one;
			}
			return null;
		}
		try {
			AffineExpression quotient = new AffineExpression();
			quotient.mConstant = mConstant.divide(divisor.mConstant);
			for (Map.Entry<String, BigDecimal> entry : mCoefficients.entrySet()) {
				BigDecimal newCoefficent = entry.getValue().divide(divisor.mConstant);
				quotient.mCoefficients.put(entry.getKey(), newCoefficent);
			}
			return quotient;
		} catch (ArithmeticException e) {
			return null;
		}
//		MathContext mc = MathContext.DECIMAL64;
//		AffineExpression quotient = new AffineExpression();
//		quotient.mConstant = mConstant.divide(divisor.mConstant, mc);
//		for (Map.Entry<String, BigDecimal> entry : mCoefficients.entrySet()) {
//			BigDecimal newCoefficent = entry.getValue().divide(divisor.mConstant, mc);
//			quotient.mCoefficients.put(entry.getKey(), newCoefficent);
//		}
//		return quotient;
	}

	@Override
	public int hashCode() {
		return 31 * mCoefficients.hashCode() + mConstant.hashCode();
	}
	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (getClass() != obj.getClass()) {
			return false;
		}
		AffineExpression other = (AffineExpression) obj;
		if (mConstant.compareTo(other.mConstant) != 0) {
			return false;
		}
		Set<String> vars = new HashSet<>();
		vars.addAll(mCoefficients.keySet());
		vars.addAll(other.mCoefficients.keySet());
		for (String v : vars) {
			if (getCoefficient(v).compareTo(other.getCoefficient(v)) != 0) {
				return false;
			}
		}
		return true;
	}

}
