/*
 * Copyright (C) 2015-2016 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;

/**
 * Represents a Boogie expression as an affine term of the form {@code Σ ( c_i * x_i ) + c} where c are constants and x
 * are variables.
 * <p>
 * This may be an equivalent transformation of the original expression. {@code null} is used when an expression cannot
 * be transformed into an affine term (either because it is not affine or we do not know if it is affine).
 * <p>
 * Objects of this class are immutable.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class AffineExpression {

	/**
	 * Map from the variables of this affine expression to their coefficients. Variables with coefficient zero are not
	 * stored.
	 */
	private final Map<IProgramVarOrConst, BigDecimal> mCoefficients;

	/**
	 * The constant summand of this affine expression.
	 */
	private BigDecimal mConstant;

	/**
	 * Constructs a new affine expression of the form {@code Σ ( c_i * x_i ) + c}.
	 *
	 * @param coefficients
	 *            Map from variables {@code x_i} to their coefficients {@code c_i}. The original map is used internally.
	 *            It may be modified by this class, but not from the outside.
	 * @param constant
	 *            Constant of summand of the affine expression.
	 */
	public AffineExpression(final Map<IProgramVarOrConst, BigDecimal> coefficients, final BigDecimal constant) {
		assert coefficients != null && constant != null;
		mCoefficients = coefficients;
		mConstant = constant;
		removeZeroSummands();
	}

	/**
	 * Constructs a new affine expression of the form {@code c}.
	 *
	 * @param constant
	 *            Constant {@code c} of the affine expression.
	 */
	public AffineExpression(final BigDecimal constant) {
		this(new HashMap<>(), constant);
	}

	/**
	 * Constructs a new affine expression of the form {@code 0}.
	 */
	private AffineExpression() {
		this(BigDecimal.ZERO);
	}

	/**
	 * Removes all entries with value {@code 0} from {@link #mCoefficients}.
	 */
	private void removeZeroSummands() {
		final Iterator<BigDecimal> iter = mCoefficients.values().iterator();
		while (iter.hasNext()) {
			if (iter.next().signum() == 0) { // "signum()" is faster than "compareTo(0)"
				iter.remove();
			}
		}
	}

	/**
	 * Returns the variables and their coefficients from this affine expression. All variables have a coefficient other
	 * than zero.
	 *
	 * @return Map from variables to their coefficients.
	 */
	public Map<IProgramVarOrConst, BigDecimal> getCoefficients() {
		return Collections.unmodifiableMap(mCoefficients);
	}

	/**
	 * Returns the coefficient of the given variable. The coefficient is 0 for variables which are not part of this
	 * affine expression.
	 *
	 * @param var
	 *            Name of a variable.
	 * @return Coefficient of the given variable.
	 */
	public BigDecimal getCoefficient(final IProgramVarOrConst var) {
		final BigDecimal factor = mCoefficients.get(var);
		return (factor == null) ? BigDecimal.ZERO : factor;
	}

	/**
	 * @return The constant summand of this affine expression.
	 */
	public BigDecimal getConstant() {
		return mConstant;
	}

	/**
	 * @return This affine expression is of the form {@code c}.
	 */
	public boolean isConstant() {
		// for (BigDecimal factor : mCoefficients.values()) {
		// if (factor.signum() != 0) {
		// return false;
		// }
		// }
		// return true;
		return mCoefficients.isEmpty();
	}

	/**
	 * Constructs an affine expression with the same variables and coefficients, but with constant 0.
	 * <p>
	 * {@code  withoutConstant(Σ ( c_i * x_i ) + c) := Σ ( c_i * x_i )}
	 *
	 * @return New version of this affine expression without constant.
	 */
	public AffineExpression withoutConstant() {
		return new AffineExpression(mCoefficients, BigDecimal.ZERO);
	}

	/**
	 * Divides this AffineExpression by a constant such that all coefficients are 1 or -1 if possible. All coefficients
	 * keep their sign.
	 * <p>
	 * Division of the constant may require rounding. Example: Unit coefficient form of (3x + 1) is (1x + 1/3), which
	 * cannot be expressed by a {@link BigDecimal}. In case rounding is required, {@code null} is returned.
	 *
	 *
	 * @return Unit coefficient form or {@code null}
	 */
	public AffineExpression unitCoefficientForm() {
		if (mCoefficients.size() == 0) {
			return this;
		} else if (absCoefficientsAreEqual()) {
			// compute constant
			final BigDecimal absCoefficient = mCoefficients.values().iterator().next().abs();
			final BigDecimal newConstant;
			try {
				newConstant = mConstant.divide(absCoefficient);
			} catch (final ArithmeticException arithException) {
				return null; // TODO switch from BigDecimal to rational numbers
			}
			// compute unit coefficients (recall: coefficients in AffineExpression are always != 0)
			final Map<IProgramVarOrConst, BigDecimal> unitCoefficients = new HashMap<>();
			mCoefficients.forEach((var, coeff) -> unitCoefficients.put(var,
					coeff.signum() > 0 ? BigDecimal.ONE : AbsIntUtil.MINUS_ONE));
			//
			return new AffineExpression(unitCoefficients, newConstant);
		} else {
			return null;
		}
	}

	/**
	 * @return All coefficients in this AffineExpression have the same absolute value.
	 */
	private boolean absCoefficientsAreEqual() {
		BigDecimal lastCoefficient = null;
		for (BigDecimal curCoefficient : mCoefficients.values()) {
			curCoefficient = curCoefficient.abs();
			if (lastCoefficient != null && curCoefficient.compareTo(lastCoefficient) != 0) {
				return false;
			}
			lastCoefficient = curCoefficient;
		}
		return true;
	}

	/**
	 * Constructs an equivalent {@link OneVarForm} of this affine expression if possible. OneVarForm is an affine
	 * expression of the form {@code +/- x + c} where {@code x} is a variable and {@code c} is a constant.
	 *
	 * @return OneVarForm of this affine expression or null.
	 */
	public OneVarForm getOneVarForm() {
		if (mCoefficients.size() != 1) {
			return null;
		}
		final Entry<IProgramVarOrConst, BigDecimal> entry = mCoefficients.entrySet().iterator().next();
		if (entry.getValue().abs().compareTo(BigDecimal.ONE) != 0) {
			return null;
		}
		final OneVarForm oneVarForm = new OneVarForm();
		oneVarForm.var = entry.getKey();
		oneVarForm.negVar = entry.getValue().signum() < 0;
		oneVarForm.constant = new OctValue(mConstant);
		return oneVarForm;
	}

	/**
	 * Constructs an equivalent {@link TwoVarForm} of this affine expression if possible. TwoVarForm is an affine
	 * expression of the form {@code +/- x_1 +/- x_2 + c} where {@code x_1, x_2} are variables and {@code c} is a
	 * constant.
	 *
	 * @return TwoVarForm of this affine expression or null.
	 */
	public TwoVarForm getTwoVarForm() {
		final int distinctVars = mCoefficients.size();
		if (distinctVars < 1 || distinctVars > 2) {
			return null;
		}
		final List<IProgramVarOrConst> vars = new ArrayList<>(distinctVars);
		final List<BigDecimal> coefficients = new ArrayList<>(distinctVars);
		mCoefficients.entrySet().forEach(entry -> {
			vars.add(entry.getKey());
			coefficients.add(entry.getValue());
		});
		if (distinctVars == 2) {
			for (final BigDecimal coefficient : coefficients) {
				if (coefficient.abs().compareTo(BigDecimal.ONE) != 0) {
					return null;
				}
			}
		} else if (coefficients.get(0).abs().compareTo(AbsIntUtil.TWO) != 0) { // && distinctVars == 1
			return null;
		}
		final TwoVarForm twoVarForm = new TwoVarForm();
		twoVarForm.var1 = vars.get(0);
		twoVarForm.negVar1 = coefficients.get(0).signum() < 0;
		if (distinctVars == 1) {
			twoVarForm.var2 = twoVarForm.var1;
			twoVarForm.negVar2 = twoVarForm.negVar1;
		} else {
			twoVarForm.var2 = vars.get(1);
			twoVarForm.negVar2 = coefficients.get(1).signum() < 0;
		}
		twoVarForm.constant = new OctValue(mConstant);
		return twoVarForm;
	}

	/**
	 * Creates a new affine expression that is the sum of this and another affine expression.
	 *
	 * @param summand
	 *            Affine expression to be added.
	 * @return {@code this + summand}
	 */
	public AffineExpression add(final AffineExpression summand) {
		final AffineExpression sum = new AffineExpression();
		sum.mConstant = mConstant.add(summand.mConstant);
		final Set<IProgramVarOrConst> vars = new HashSet<>();
		vars.addAll(mCoefficients.keySet());
		vars.addAll(summand.mCoefficients.keySet());
		for (final IProgramVarOrConst v : vars) {
			final BigDecimal sumFactor = getCoefficient(v).add(summand.getCoefficient(v));
			sum.mCoefficients.put(v, sumFactor);
		}
		sum.removeZeroSummands();
		return sum;
	}

	/**
	 * Creates a new affine expression that is the difference of this and another affine expression.
	 *
	 * @param summand
	 *            Affine expression to be added.
	 * @return {@code this - summand}
	 */
	public AffineExpression subtract(final AffineExpression subtrahend) {
		return add(subtrahend.negate()); // negate() never returns null
	}

	/**
	 * Creates a new affine expression that is the negation of this affine expression.
	 *
	 * @return {@code -this}
	 */
	public AffineExpression negate() {
		final AffineExpression negation = new AffineExpression();
		negation.mConstant = mConstant.negate();
		for (final Entry<IProgramVarOrConst, BigDecimal> entry : mCoefficients.entrySet()) {
			negation.mCoefficients.put(entry.getKey(), entry.getValue().negate());
		}
		return negation;
	}

	/**
	 * Creates a new affine expression that is the product of this and another affine expression, if the product is
	 * affine.
	 *
	 * @param factor
	 *            Affine expression to be multiplicated.
	 * @return {@code this * factor} or {@code null}
	 */
	public AffineExpression multiply(final AffineExpression factor) {
		final AffineExpression affineFactor;
		final AffineExpression constantFactor;
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
		final AffineExpression product = new AffineExpression();
		product.mConstant = affineFactor.mConstant.multiply(constantFactor.mConstant);
		for (final Entry<IProgramVarOrConst, BigDecimal> entry : affineFactor.mCoefficients.entrySet()) {
			final BigDecimal newCoefficent = entry.getValue().multiply(constantFactor.mConstant);
			product.mCoefficients.put(entry.getKey(), newCoefficent);
		}
		return product;
	}

	/**
	 * Creates a new affine expression that is the quotient of this and another affine expression, if the quotient is
	 * affine.
	 *
	 * @param divisor
	 *            Affine expression dividing this affine expression.
	 * @param integerDivison
	 *            Calculate the euclidean integer division.
	 * @return {@code this / divisor} or {@code null}
	 */
	public AffineExpression divide(final AffineExpression divisor, final boolean integerDivison) {
		if (divisor.isConstant()) {
			try {
				return divideByConstant(divisor.mConstant, integerDivison);
			} catch (final ArithmeticException e) {
				// return null (see below)
			}
		}
		return null;
	}

	/**
	 * Creates a new affine expression that is the quotient of this and a constant, if the quotient is affine.
	 *
	 * @param divisor
	 *            Constant dividing this affine expression.
	 * @param integerDivison
	 *            Calculate the euclidean integer division.
	 * @return {@code this / divisor}
	 *
	 * @throws ArithmeticException
	 *             The quotient could not be transformed into an affine expression.
	 */
	private AffineExpression divideByConstant(final BigDecimal divisor, final boolean integerDivison) {
		if (isConstant()) {
			final BigDecimal quotient;
			if (integerDivison) {
				quotient = AbsIntUtil.euclideanDivision(mConstant, divisor);
			} else {
				quotient = mConstant.divide(divisor);
			}
			return new AffineExpression(quotient);
		}
		final BiFunction<BigDecimal, BigDecimal, BigDecimal> divOp =
				integerDivison ? AbsIntUtil::exactDivison : BigDecimal::divide;
		final AffineExpression quotient = new AffineExpression();
		quotient.mConstant = divOp.apply(mConstant, divisor);
		for (final Entry<IProgramVarOrConst, BigDecimal> entry : mCoefficients.entrySet()) {
			final BigDecimal newCoefficent = divOp.apply(entry.getValue(), divisor);
			quotient.mCoefficients.put(entry.getKey(), newCoefficent);
		}
		return quotient;
	}

	/**
	 * Creates a new affine expression that is the remainder of the euclidean division of this and another affine
	 * expression, if the quotient is affine.
	 *
	 * @param divisor
	 *            Constant dividing this affine expression.
	 * @param integerDivison
	 *            Calculate the remainder of the euclidean integer division.
	 * @return {@code this % divisor} or {@code null}
	 */
	public AffineExpression modulo(final AffineExpression divisor) {
		if (isConstant() && divisor.isConstant() && divisor.mConstant.signum() != 0) {
			return new AffineExpression(AbsIntUtil.euclideanModulo(mConstant, divisor.mConstant));
		}
		return null;
	}

	@Override
	public int hashCode() {
		return 31 * mCoefficients.hashCode() + mConstant.hashCode();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (getClass() != obj.getClass()) {
			return false;
		}
		final AffineExpression other = (AffineExpression) obj;
		if (mConstant.compareTo(other.mConstant) != 0) {
			return false;
		}
		final Set<IProgramVarOrConst> vars = new HashSet<>();
		vars.addAll(mCoefficients.keySet());
		vars.addAll(other.mCoefficients.keySet());
		for (final IProgramVarOrConst v : vars) {
			final BigDecimal coeff = getCoefficient(v);
			final BigDecimal otherCoeff = other.getCoefficient(v);
			if (coeff.compareTo(otherCoeff) != 0) {
				return false;
			}
		}
		return true;
	}

	@Override
	public String toString() {
		final StringBuilder strBuilder = new StringBuilder();
		for (final Entry<IProgramVarOrConst, BigDecimal> entry : mCoefficients.entrySet()) {
			strBuilder.append(entry.getValue());
			// multiplication dot
			strBuilder.append('\u22C5');
			strBuilder.append(entry.getKey());
			strBuilder.append(" + ");
		}
		strBuilder.append(mConstant);
		return strBuilder.toString();
	}

	/** @see AffineExpression#getOneVarForm() */
	public static class OneVarForm {
		public IProgramVarOrConst var;
		public boolean negVar;
		public OctValue constant;
	}

	/**
	 * Affine expression of the form
	 * <i>(±var1) + (±var2) + c</i>.
	 * @see AffineExpression#getTwoVarForm()
	 */
	public static class TwoVarForm {
		public IProgramVarOrConst var1, var2;
		public boolean negVar2, negVar1;
		public OctValue constant;
	}
}
