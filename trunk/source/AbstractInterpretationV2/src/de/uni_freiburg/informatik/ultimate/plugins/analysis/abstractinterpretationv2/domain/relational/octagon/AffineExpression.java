package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
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
			if (iter.next().signum() == 0) { // "signum()" is faster than "compareTo(0)"
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
//		for (BigDecimal factor : mCoefficients.values()) {
//			if (factor.signum() != 0) {
//				return false;
//			}
//		}
//		return true;
		return mCoefficients.isEmpty();
	}

	public AffineExpression withoutConstant() {
		return new AffineExpression(mCoefficients, BigDecimal.ZERO);
	}
	
	public static class OneVarForm {
		public String var;
		public boolean negVar;
		public OctValue constant;
	}

	public OneVarForm getOneVarForm() {
		if (mCoefficients.size() != 1) {
			return null;
		}
		OneVarForm oneVarForm = new OneVarForm();
		Map.Entry<String, BigDecimal> entry = mCoefficients.entrySet().iterator().next();
		if (entry.getValue().abs().compareTo(BigDecimal.ONE) != 0) {
			return null;
		}
		oneVarForm.var = entry.getKey();
		oneVarForm.negVar = entry.getValue().signum() < 0;
		oneVarForm.constant = new OctValue(mConstant);
		return oneVarForm;
	}
	
	public static class TwoVarForm {
		public String var1, var2;
		public boolean negVar2, negVar1;
		public OctValue constant;
	}
	
	public TwoVarForm getTwoVarForm() {
		if (mCoefficients.size() != 2) {
			return null;
		}
		List<String> vars = new ArrayList<>(2);
		List<BigDecimal> coefficients = new ArrayList<>(2);
		mCoefficients.entrySet().forEach(entry -> {
			vars.add(entry.getKey());
			coefficients.add(entry.getValue());
		});
		TwoVarForm twoVarForm = new TwoVarForm();
		for (BigDecimal d : coefficients) {
			if (d.abs().compareTo(BigDecimal.ONE) != 0) {
				return null;
			}
		}
		twoVarForm.var1 = vars.get(0);
		twoVarForm.var2 = vars.get(1);
		twoVarForm.negVar1 = coefficients.get(0).signum() < 0;
		twoVarForm.negVar2 = coefficients.get(1).signum() < 0;
		twoVarForm.constant = new OctValue(mConstant);
		return twoVarForm;
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
	
	public AffineExpression subtract(AffineExpression subtrahend) {
		return this.add(subtrahend.negate()); // negate() never returns null
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
				return divideByConstant(divisor.mConstant, integerDivison);
			} else {
				return divideByNonConstant(divisor, integerDivison);
			}
		} catch (ArithmeticException e) {
		}
		return null;
	}

	private AffineExpression divideByConstant(BigDecimal divisor, boolean integerDivison) {
		if (integerDivison) {
			if (isConstant()) {
				return new AffineExpression(NumUtil.euclideanDivision(mConstant, divisor));
			} else {
				return null;
			}
		} else {
			AffineExpression quotient = new AffineExpression();
			quotient.mConstant = mConstant.divide(divisor);
			for (Map.Entry<String, BigDecimal> entry : mCoefficients.entrySet()) {
				BigDecimal newCoefficent = entry.getValue().divide(divisor);
				quotient.mCoefficients.put(entry.getKey(), newCoefficent);
			}
			return quotient;
		}
	}
	
	// Also allows to divide by constants, but returns null more often.
	// divideByConstant may return an AfffineTerm where this returns null.
	// The result will always be a constant.
	// Supports only:    c*AE / AE  =  c
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
