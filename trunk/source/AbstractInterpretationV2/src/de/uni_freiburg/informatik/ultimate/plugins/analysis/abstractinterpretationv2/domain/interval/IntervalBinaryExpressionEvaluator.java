/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * The binary expression evaluator of the interval domain.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class IntervalBinaryExpressionEvaluator implements INAryEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> {

	protected IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> mLeftSubEvaluator;
	protected IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> mRightSubEvaluator;

	protected final Set<String> mVariableSet;

	protected final Logger mLogger;
	private Operator mOperator;

	/**
	 * Creates an instance of the binary expression evaluator of the interval domain.
	 * 
	 * @param services
	 */
	protected IntervalBinaryExpressionEvaluator(IUltimateServiceProvider services) {
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mVariableSet = new HashSet<String>();
	}

	/**
	 * Internal constructor for testing reasons. Not accessible from outside of the package.
	 * 
	 * <p>
	 * <b>Note:</b> This constructor is for testing purposes only and is not supposed to be called outside of the unit
	 * tests as it does not instanciate the class correctly.
	 * </p>
	 */
	IntervalBinaryExpressionEvaluator() {
		mLogger = null;
		mVariableSet = new HashSet<String>();
	}

	@Override
	public IEvaluationResult<IntervalDomainValue> evaluate(IAbstractState<CodeBlock, BoogieVar> currentState) {

		assert currentState != null;

		for (String var : mLeftSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}
		for (String var : mRightSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}

		final IEvaluationResult<IntervalDomainValue> firstResult = mLeftSubEvaluator.evaluate(currentState);
		final IEvaluationResult<IntervalDomainValue> secondResult = mRightSubEvaluator.evaluate(currentState);

		switch (mOperator) {
		case ARITHPLUS:
			return performAddition(firstResult, secondResult);
		case ARITHMINUS:
			return performSubtraction(firstResult, secondResult);
		case ARITHMUL:
			return performMultiplication(firstResult, secondResult);
		default:
			throw new UnsupportedOperationException("The operator " + mOperator.toString() + " is not implemented.");
		}
	}

	/**
	 * Adds two {@link IntervalDomainValue}s following the scheme:
	 * 
	 * <p>
	 * <ul>
	 * <li>[a, b] + [c, d] = [a + c, b + d]</li>
	 * </ul>
	 * </p>
	 * 
	 * @param firstResult
	 *            The first interval.
	 * @param secondResult
	 *            The second interval.
	 * @return A new evaluation result corresponding to the addition of the two input intervals.
	 */
	private IEvaluationResult<IntervalDomainValue> performAddition(IEvaluationResult<IntervalDomainValue> firstResult,
	        IEvaluationResult<IntervalDomainValue> secondResult) {

		assert firstResult != null;
		assert secondResult != null;

		if (firstResult.getResult().isBottom() || secondResult.getResult().isBottom()) {
			return new IntervalDomainValue(true);
		}

		if (firstResult.getResult().isInfinity() || secondResult.getResult().isInfinity()) {
			return new IntervalDomainValue();
		}

		IntervalValue lowerBound = new IntervalValue();
		IntervalValue upperBound = new IntervalValue();

		// Compute lower bound
		if (firstResult.getResult().getLower().isInfinity() || secondResult.getResult().getLower().isInfinity()) {
			lowerBound.setToInfinity();
		} else {
			lowerBound.setValue(
			        firstResult.getResult().getLower().getValue().add(secondResult.getResult().getLower().getValue()));
		}

		// Compute upper bound
		if (firstResult.getResult().getUpper().isInfinity() || secondResult.getResult().getUpper().isInfinity()) {
			upperBound.setToInfinity();
		} else {
			upperBound.setValue(
			        firstResult.getResult().getUpper().getValue().add(secondResult.getResult().getUpper().getValue()));
		}

		return new IntervalDomainValue(lowerBound, upperBound);
	}

	/**
	 * Computes the subtraction of two {@link IntervalDomainValue}s following the scheme:
	 * <p>
	 * <ul>
	 * <li>[a, b] - [c, d] = [a - d, b - c]</li>
	 * </ul>
	 * </p>
	 * 
	 * @param firstResult
	 *            The first interval.
	 * @param secondResult
	 *            The second interval.
	 * @return A new interval representing the result of <code>firstResult</code> - <code>secondResult</code>.
	 */
	private IEvaluationResult<IntervalDomainValue> performSubtraction(
	        IEvaluationResult<IntervalDomainValue> firstResult, IEvaluationResult<IntervalDomainValue> secondResult) {
		assert firstResult != null;
		assert secondResult != null;

		if (firstResult.getResult().isBottom() || secondResult.getResult().isBottom()) {
			return new IntervalDomainValue(true);
		}

		if (firstResult.getResult().isInfinity() || secondResult.getResult().isInfinity()) {
			return new IntervalDomainValue();
		}

		IntervalValue lowerBound = new IntervalValue();
		IntervalValue upperBound = new IntervalValue();

		// Compute lower bound
		if (firstResult.getResult().getLower().isInfinity() || secondResult.getResult().getUpper().isInfinity()) {
			lowerBound.setToInfinity();
		} else {
			lowerBound.setValue(firstResult.getResult().getLower().getValue()
			        .subtract(secondResult.getResult().getUpper().getValue()));
		}

		// Compute upper bound
		if (firstResult.getResult().getUpper().isInfinity() || secondResult.getResult().getLower().isInfinity()) {
			upperBound.setToInfinity();
		} else {
			upperBound.setValue(firstResult.getResult().getUpper().getValue()
			        .subtract(secondResult.getResult().getLower().getValue()));
		}

		return new IntervalDomainValue(lowerBound, upperBound);
	}

	/**
	 * Computes the result of the multiplication of two {@link IntervalDomainValue}s following the scheme:
	 * 
	 * <p>
	 * <ul>
	 * <li>[a, b] * [c, d] = [min(a*c, a*d, b*c, b*d), max(a*c, a*d, b*c, b*d)]</li>
	 * </ul>
	 * </p>
	 * 
	 * @param firstResult
	 *            The first interval.
	 * @param secondResult
	 *            The second interval.
	 * @return A new interval representing the result of <code>firstResult</code> * <code>secondRestult</code>.
	 */
	private IEvaluationResult<IntervalDomainValue> performMultiplication(
	        IEvaluationResult<IntervalDomainValue> firstResult, IEvaluationResult<IntervalDomainValue> secondResult) {
		assert firstResult != null;
		assert secondResult != null;

		if (firstResult.getResult().isBottom() || secondResult.getResult().isBottom()) {
			return new IntervalDomainValue(true);
		}

		// Note: No check for infinite intervals here, since a multiplication with 0 would result in too coarse results.

		IntervalValue lowerBound = computeMinMult(firstResult.getResult(), secondResult.getResult());
		IntervalValue upperBound = computeMaxMult(firstResult.getResult(), secondResult.getResult());

		return new IntervalDomainValue(lowerBound, upperBound);
	}

	/**
	 * Computes the maximum value of the multiplication of two intervals:
	 * 
	 * <p>
	 * [a, b] and [c, d]: max(ac, ad, bc, bd).
	 * </p>
	 * 
	 * @param first
	 *            The first interval of the form [a, b].
	 * @param second
	 *            The second interval of the form [c, d].
	 * @return max(ac, ad, bc, bd).
	 */
	private IntervalValue computeMaxMult(IntervalDomainValue first, IntervalDomainValue second) {

		IntervalValue returnValue = new IntervalValue();
		boolean valuePresent = false;

		// If both intervals are infinite, the maximum is \infty.
		if (first.isInfinity() && second.isInfinity()) {
			return new IntervalValue();
		}

		// Compute a*c
		if (first.getLower().isInfinity()) {

			// -\infty * -\infty = \infty
			if (second.getLower().isInfinity()) {
				return new IntervalValue();
			} else {
				// -\infty * val = \infty, if val < 0
				if (second.getLower().getValue().signum() < 0) {
					return new IntervalValue();
				}

				// -\infty * 0 = 0
				if (second.getLower().getValue().signum() == 0) {
					returnValue = updateIfLarger(returnValue, new BigDecimal(0), valuePresent);
					valuePresent = true;
				}
			}
		} else {
			if (second.getLower().isInfinity()) {
				// val * -\infty = \infty, if val > 0
				if (first.getLower().getValue().signum() < 0) {
					return new IntervalValue();
				}

				// 0 * -\infty = 0
				if (first.getLower().getValue().signum() == 0) {
					returnValue = updateIfLarger(returnValue, new BigDecimal(0), valuePresent);
					valuePresent = true;
				}
			} else {
				returnValue = updateIfLarger(returnValue,
				        first.getLower().getValue().multiply(second.getLower().getValue()), valuePresent);
				valuePresent = true;
			}
		}

		// Compute a*d
		if (first.getLower().isInfinity()) {
			if (!second.getUpper().isInfinity()) {
				// -\infty * val = \infty, if val < 0
				if (second.getUpper().getValue().signum() < 0) {
					return new IntervalValue();
				}

				// -\infty * 0 = 0
				if (second.getUpper().getValue().signum() == 0) {
					returnValue = updateIfLarger(returnValue, new BigDecimal(0), valuePresent);
					valuePresent = true;
				}
			}
		} else {

			if (second.getUpper().isInfinity()) {
				// val * \infty = \infty, if val > 0
				if (first.getLower().getValue().signum() > 0) {
					return new IntervalValue();
				}

				// 0 * anything = 0
				if (first.getLower().getValue().signum() == 0) {
					returnValue = updateIfLarger(returnValue, new BigDecimal(0), valuePresent);
					valuePresent = true;
				}
			} else {
				returnValue = updateIfLarger(returnValue,
				        first.getLower().getValue().multiply(second.getUpper().getValue()), valuePresent);
				valuePresent = true;
			}
		}

		// Compute b*c
		if (first.getUpper().isInfinity()) {
			if (!second.getLower().isInfinity()) {
				// \infty * val = \infty, if val > 0
				if (second.getLower().getValue().signum() > 0) {
					return new IntervalValue();
				}

				// \infty * 0 = 0
				if (second.getLower().getValue().signum() == 0) {
					returnValue = updateIfLarger(returnValue, new BigDecimal(0), valuePresent);
					valuePresent = true;
				}
			}
		} else {
			if (second.getLower().isInfinity()) {
				// val * -\infty = \infty, if val < 0
				if (first.getUpper().getValue().signum() < 0) {
					return new IntervalValue();
				}

				// 0 * anything = 0
				if (first.getUpper().getValue().signum() == 0) {
					returnValue = updateIfLarger(returnValue, new BigDecimal(0), valuePresent);
					valuePresent = true;
				}
			} else {
				returnValue = updateIfLarger(returnValue,
				        first.getUpper().getValue().multiply(second.getLower().getValue()), valuePresent);
				valuePresent = true;
			}
		}

		// Compute b*d
		if (first.getUpper().isInfinity()) {
			// \infty * \infty = \infty
			if (second.getUpper().isInfinity()) {
				return new IntervalValue();
			} else {
				// \infty * val = \infty, if val > 0
				if (second.getUpper().getValue().signum() > 0) {
					return new IntervalValue();
				}

				// \infty * 0 = 0
				if (second.getUpper().getValue().signum() == 0) {
					returnValue = updateIfLarger(returnValue, new BigDecimal(0), valuePresent);
					valuePresent = true;
				}
			}
		} else {
			if (second.getUpper().isInfinity()) {
				// val * \infty = \infty, if val > 0
				if (first.getUpper().getValue().signum() > 0) {
					return new IntervalValue();
				}

				// 0 * \infty = 0
				if (first.getUpper().getValue().signum() == 0) {
					returnValue = updateIfLarger(returnValue, new BigDecimal(0), valuePresent);
					valuePresent = true;
				}
			} else {
				returnValue = updateIfLarger(returnValue,
				        first.getUpper().getValue().multiply(second.getUpper().getValue()), valuePresent);
				valuePresent = true;
			}
		}

		assert valuePresent;
		return returnValue;
	}

	/**
	 * Computes the minimum value of the multiplication of two intervals:
	 * 
	 * <p>
	 * [a, b] and [c, d]: min(ac, ad, bc, bd).
	 * </p>
	 * 
	 * @param first
	 *            The first interval of the form [a, b].
	 * @param second
	 *            The second interval of the form [c, d].
	 * @return min(ac, ad, bc, bd).
	 */
	private IntervalValue computeMinMult(IntervalDomainValue first, IntervalDomainValue second) {

		IntervalValue returnValue = new IntervalValue();
		boolean valuePresent = false;

		// If both intervals are infinite, the minimum is -\infty.
		if (first.isInfinity() && second.isInfinity()) {
			return new IntervalValue();
		}

		// Compute a*c
		if (first.getLower().isInfinity()) {
			if (!second.getLower().isInfinity()) {

				// -\infty * val = -\infty, if val > 0.
				if (second.getLower().getValue().signum() > 0) {
					return new IntervalValue();
				}

				// -\infty * val = 0, if val = 0.
				if (second.getLower().getValue().signum() == 0) {
					returnValue = updateIfSmaller(returnValue, new BigDecimal(0), valuePresent);
					valuePresent = true;
				}
			}
		} else {

			// 0 * anything = 0.
			if (first.getLower().getValue().signum() == 0) {
				returnValue = updateIfSmaller(returnValue, new BigDecimal(0), valuePresent);
				valuePresent = true;
			} else {
				if (second.getLower().isInfinity()) {

					// val * -\infty = -\infty, if val > 0
					if (first.getLower().getValue().signum() > 0) {
						return new IntervalValue();
					}
				} else {
					returnValue = updateIfSmaller(returnValue,
					        first.getLower().getValue().multiply(second.getLower().getValue()), valuePresent);
					valuePresent = true;
				}
			}
		}

		// Compute a*d
		if (first.getLower().isInfinity()) {

			// -\infty * \infty = -\infty
			if (second.getUpper().isInfinity()) {
				return new IntervalValue();
			}

			// -\infty * val = -\infty, if val > 0
			if (second.getUpper().getValue().signum() > 0) {
				return new IntervalValue();
			}

			// anything * 0 = 0.
			if (second.getUpper().getValue().signum() == 0) {
				returnValue = updateIfSmaller(returnValue, new BigDecimal(0), valuePresent);
				valuePresent = true;
			}
		} else {

			// 0 * anything = 0
			if (first.getLower().getValue().signum() == 0) {
				returnValue = updateIfSmaller(returnValue, new BigDecimal(0), valuePresent);
				valuePresent = true;
			} else {
				if (second.getUpper().isInfinity()) {

					// val * \infty = -\infty, if val < 0
					if (first.getLower().getValue().signum() < 0) {
						return new IntervalValue();
					}
				} else {
					returnValue = updateIfSmaller(returnValue,
					        first.getLower().getValue().multiply(second.getUpper().getValue()), valuePresent);
					valuePresent = true;
				}
			}
		}

		// Compute b*c
		if (first.getUpper().isInfinity()) {

			// \infty * -\infty = -\infty
			if (second.getLower().isInfinity()) {
				return new IntervalValue();
			}

			// \infty * val = -\infty, if val < 0
			if (second.getLower().getValue().signum() < 0) {
				return new IntervalValue();
			}

			// \infty * 0 = 0
			if (second.getLower().getValue().signum() == 0) {
				returnValue = updateIfSmaller(returnValue, new BigDecimal(0), valuePresent);
				valuePresent = true;
			}
		} else {
			if (second.getLower().isInfinity()) {
				// val * -\infty = -\infty, if val > 0
				if (first.getUpper().getValue().signum() > 0) {
					return new IntervalValue();
				}

				// 0 * anything = 0
				if (first.getUpper().getValue().signum() == 0) {
					returnValue = updateIfSmaller(returnValue, new BigDecimal(0), valuePresent);
					valuePresent = true;
				}
			} else {
				returnValue = updateIfSmaller(returnValue,
				        first.getUpper().getValue().multiply(second.getLower().getValue()), valuePresent);
				valuePresent = true;
			}
		}

		// Compute b * d
		if (first.getUpper().isInfinity()) {
			if (!second.getUpper().isInfinity()) {

				// \infty * val = -\infty, if val < 0
				if (second.getUpper().getValue().signum() < 0) {
					return new IntervalValue();
				}

				if (second.getUpper().getValue().signum() == 0) {
					returnValue = updateIfSmaller(returnValue, new BigDecimal(0), valuePresent);
					valuePresent = true;
				}
			}
		} else {
			if (second.getUpper().isInfinity()) {
				// val * \infty = -\infty, if val < 0
				if (first.getUpper().getValue().signum() < 0) {
					return new IntervalValue();
				}

				// 0 * \infty = 0
				if (first.getUpper().getValue().signum() == 0) {
					returnValue = updateIfSmaller(returnValue, new BigDecimal(0), valuePresent);
					valuePresent = true;
				}
			} else {
				returnValue = updateIfSmaller(returnValue,
				        first.getUpper().getValue().multiply(second.getLower().getValue()), valuePresent);
				valuePresent = true;
			}
		}

		assert valuePresent;
		return returnValue;
	}

	private IntervalValue updateIfSmaller(IntervalValue oldValue, BigDecimal newValue, boolean valuePresent) {
		if (valuePresent) {
			if (oldValue.getValue().compareTo(newValue) >= 0) {
				return new IntervalValue(newValue);
			} else {
				return oldValue;
			}
		} else {
			return new IntervalValue(newValue);
		}
	}

	private IntervalValue updateIfLarger(IntervalValue oldValue, BigDecimal newValue, boolean valuePresent) {
		if (valuePresent) {
			if (oldValue.getValue().compareTo(newValue) <= 0) {
				return new IntervalValue(newValue);
			} else {
				return oldValue;
			}
		} else {
			return new IntervalValue(newValue);
		}
	}

	@Override
	public void addSubEvaluator(IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> evaluator) {
		if (mLeftSubEvaluator != null && mRightSubEvaluator != null) {
			throw new UnsupportedOperationException("There are no free sub evaluators left to be assigned.");
		}

		if (mLeftSubEvaluator == null) {
			mLeftSubEvaluator = evaluator;
			return;
		}

		mRightSubEvaluator = evaluator;

	}

	@Override
	public Set<String> getVarIdentifiers() {
		return mVariableSet;
	}

	@Override
	public boolean hasFreeOperands() {
		return (mLeftSubEvaluator == null || mRightSubEvaluator == null);
	}

	@Override
	public void setOperator(Object operator) {
		assert operator != null;
		assert operator instanceof Operator;

		mOperator = (Operator) operator;
	}
}
