package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.NumUtil;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.lpsolver.LinearConstraint;

/**
 * Represents a Boogie expression as an affine term of the form
 * {@code Σ ( c_i * x_i ) + c} where c are constants and x are variables.
 * <p>
 * This may be an equivalent transformation of the original expression.
 * {@code null} is used when an expression cannot be transformed into an
 * affine term (either because it is not affine or we don't know if it is affine).
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class AffineExpression {

	public static class SimpleForm {
		public static final int MAX_VARS = 2;
		public String[] var = new String[MAX_VARS];
		public boolean[] isVarPositive = new boolean[MAX_VARS];
		public OctValue constant;
	}
	
	/**
	 * Map from the variables of this affine expression to their coefficients.
	 * Variables with coefficient zero aren't stored.
	 */
	private Map<String, BigDecimal> mCoefficients;
	
	/**
	 * The constant summand of this affine expression.
	 */
	private BigDecimal mConstant;
	
	public AffineExpression(Map<String, BigDecimal> coefficients, BigDecimal constant) {
		assert coefficients != null && constant != null;
		mCoefficients = coefficients;
		mConstant = constant;
		removeZeroSummands();
	}

	public AffineExpression(BigDecimal constant) {
		this(new HashMap<>(), constant);
	}
	
	private AffineExpression() {
		this(BigDecimal.ZERO);
	}
	
	private void removeZeroSummands() {
		Iterator<BigDecimal> iter = mCoefficients.values().iterator();
		while (iter.hasNext()) {
			if (iter.next().signum() == 0) { // "signum()" is faster than "comparTo(0)"
				iter.remove();
			}
		}
	}
	
	public Map<String, BigDecimal> getCoefficients() {
		return Collections.unmodifiableMap(mCoefficients);
	}

	public BigDecimal getCoefficient(String var) {
		BigDecimal factor = mCoefficients.get(var);
		return (factor == null) ? BigDecimal.ZERO : factor;
	}

	public BigDecimal getConstant() {
		return mConstant;
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

	public SimpleForm simpleForm() {
		BigDecimal minusOne = BigDecimal.ONE.negate();
		SimpleForm sf = new SimpleForm();
		int i = 0;
		for (Map.Entry<String, BigDecimal> entry : mCoefficients.entrySet()) {
			if (i >= SimpleForm.MAX_VARS) {
				return null;
			} 
			BigDecimal coeff = entry.getValue();
			if (coeff.compareTo(BigDecimal.ONE) != 0) {
				sf.isVarPositive[i] = true;
			} else if (coeff.compareTo(minusOne) != 0) {
				sf.isVarPositive[i] = false;
			} else {
				return null;
			}
			sf.var[i] = entry.getKey();
			++i;
		}
		sf.constant = new OctValue(mConstant);
		return sf;
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
		if (constantFactor.mConstant.signum() == 0) {
			return new AffineExpression();
		}
		AffineExpression product = new AffineExpression();
		product.mConstant = affineFactor.mConstant.multiply(constantFactor.mConstant);
		for (Map.Entry<String, BigDecimal> entry : affineFactor.mCoefficients.entrySet()) {
			BigDecimal newCoefficent = entry.getValue().multiply(constantFactor.mConstant);
			product.mCoefficients.put(entry.getKey(), newCoefficent);
		}
		return product;
	}

	public AffineExpression divide(AffineExpression divisor, boolean integerDivison) {
		try {
			if (divisor.isConstant()) {
				return divideByConstant(divisor, integerDivison);
			} else {
				return divideByNonConstant(divisor, integerDivison);
			}
		} catch (ArithmeticException e) {
		}
		return null;
	}

	private AffineExpression divideByConstant(AffineExpression divisor, boolean integerDivison) {
		assert divisor.isConstant();
		AffineExpression quotient = new AffineExpression();
		BiFunction<BigDecimal, BigDecimal, BigDecimal> divOp =
				integerDivison ? NumUtil::euclideanDivision : BigDecimal::divide;
		quotient.mConstant = divOp.apply(mConstant, divisor.mConstant);
		for (Map.Entry<String, BigDecimal> entry : mCoefficients.entrySet()) {
			BigDecimal newCoefficent = divOp.apply(entry.getValue(), divisor.mConstant);
			quotient.mCoefficients.put(entry.getKey(), newCoefficent);
		}
		return quotient;
	}
	
	// also allows to divide by constants, but returns null more often
	// divide by constant may return an AfffineTerm where this doesn't
	// the result will always be a constant
	private AffineExpression divideByNonConstant(AffineExpression divisor, boolean integerDivison) {
		Set<String> vars = mCoefficients.keySet();
		if (!vars.equals(divisor.mCoefficients.keySet())) {
			return null;
		}
		BiFunction<BigDecimal, BigDecimal, BigDecimal> divOp =
				integerDivison ? NumUtil::exactDivison : BigDecimal::divide;
		BigDecimal qFixed = null;
		if (divisor.mConstant.signum() != 0) {
			qFixed = divOp.apply(mConstant, divisor.mConstant);
		} else if (mConstant.signum() != 0) {
			return null; // (x + c) / (x + 0) is not affine
		}
		for (String v : vars) {
			BigDecimal c = mCoefficients.get(v);
			BigDecimal d = divisor.mCoefficients.get(v);
			BigDecimal q = divOp.apply(c, d);
			if (qFixed == null) {
				qFixed = q;
			} else if (q.compareTo(qFixed) != 0) {
				return null;
			}
		}
		return new AffineExpression(qFixed);
	}
	
	public AffineExpression modulo(AffineExpression divisor) {
		if (isConstant() && divisor.isConstant() && divisor.mConstant.signum() != 0) {
			return new AffineExpression(NumUtil.euclideanModulo(mConstant, divisor.mConstant));
		}
		return null;
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

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (Map.Entry<String, BigDecimal> entry : mCoefficients.entrySet()) {
			sb.append(entry.getValue());
			sb.append("\u22C5"); // multiplication dot
			sb.append(entry.getKey());
			sb.append(" + ");
		}
		sb.append(mConstant);
		return sb.toString();
	}

	public LinearConstraint<BigDecimal> constraintGreaterEqualZero() {
		LinearConstraint<BigDecimal> c = baseConstraintWithoutConstant();
		c.setLower(mConstant.negate());
		return c;
	}

	public LinearConstraint<BigDecimal> constraintLessEqualZero() {
		LinearConstraint<BigDecimal> c = baseConstraintWithoutConstant();
		c.setUpper(mConstant.negate());
		return c;
	}

	public LinearConstraint<BigDecimal> constraintEqualZero() {
		LinearConstraint<BigDecimal> c = baseConstraintWithoutConstant();
		BigDecimal bound = mConstant.negate();
		c.setLower(bound);
		c.setUpper(bound);
		return c;
	}

	private LinearConstraint<BigDecimal> baseConstraintWithoutConstant() {
		LinearConstraint<BigDecimal> c = new LinearConstraint<>("unnamed");
		for (Map.Entry<String, BigDecimal> entry : mCoefficients.entrySet()) {
			c.addCoefficient(entry.getKey(), entry.getValue());
		}
		return c;
	}
}
