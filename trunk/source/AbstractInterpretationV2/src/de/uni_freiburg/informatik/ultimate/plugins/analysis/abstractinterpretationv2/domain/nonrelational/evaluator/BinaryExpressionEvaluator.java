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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;

/**
 * Standard binary expression evaluator for Abstract Interpretation for Nonrelational Domain States.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <VALUE>
 *            The value type of the domain.
 * @param <STATE>
 *            The state type of the domain.
 */
public class BinaryExpressionEvaluator<VALUE extends INonrelationalValue<VALUE>, STATE extends IAbstractState<STATE>>
		extends NAryEvaluator<VALUE, STATE> {

	private final EvaluatorLogger mLogger;
	private final EvaluatorType mEvaluatorType;
	private final int mMaxParallelSates;

	private final INonrelationalValueFactory<VALUE> mNonrelationalValueFactory;

	private Operator mOperator;

	private final VALUE mTopValue;

	public BinaryExpressionEvaluator(final EvaluatorLogger logger, final EvaluatorType type,
			final int maxParallelStates, final int maxRecursionDepth,
			final INonrelationalValueFactory<VALUE> nonrelationalValueFactory) {
		super(maxRecursionDepth, nonrelationalValueFactory, logger);
		mLogger = logger;
		mEvaluatorType = type;
		mMaxParallelSates = maxParallelStates;
		mNonrelationalValueFactory = nonrelationalValueFactory;
		mTopValue = mNonrelationalValueFactory.createTopValue();
	}

	@Override
	public Collection<IEvaluationResult<VALUE>> evaluate(final STATE currentState) {
		assert currentState != null;

		final Collection<IEvaluationResult<VALUE>> returnList = new ArrayList<>();

		final Collection<IEvaluationResult<VALUE>> firstResult =
				getSubEvaluator(0).evaluate(currentState, getCurrentEvaluationRecursion() + 1);
		final Collection<IEvaluationResult<VALUE>> secondResult =
				getSubEvaluator(1).evaluate(currentState, getCurrentEvaluationRecursion() + 1);

		for (final IEvaluationResult<VALUE> res1 : firstResult) {
			for (final IEvaluationResult<VALUE> res2 : secondResult) {
				final Collection<IEvaluationResult<VALUE>> result = evaluate(mOperator, res1, res2);
				mLogger.logEvaluation(mOperator, result, res1, res2);
				returnList.addAll(result);
			}
		}
		assert !returnList.isEmpty();
		return NonrelationalUtils.mergeIfNecessary(returnList, mMaxParallelSates);
	}

	private Collection<IEvaluationResult<VALUE>> evaluate(final Operator op, final IEvaluationResult<VALUE> first,
			final IEvaluationResult<VALUE> second) {

		final VALUE firstValue = first.getValue();
		final VALUE secondValue = second.getValue();
		switch (op) {
		case ARITHPLUS:
			return onlyValue(firstValue.add(secondValue));
		case ARITHMINUS:
			return onlyValue(firstValue.subtract(secondValue));
		case ARITHMUL:
			return onlyValue(firstValue.multiply(secondValue));
		case ARITHDIV:
			return evaluateArithDiv(first, second);
		case ARITHMOD:
			assert mEvaluatorType == EvaluatorType.INTEGER : "Type error: modulo is not defined on reals";
			return onlyValue(firstValue.modulo(secondValue));
		case LOGICAND:
			return onlyBoolean(first.getBooleanValue().and(second.getBooleanValue()));
		case LOGICOR:
			return onlyBoolean(first.getBooleanValue().or(second.getBooleanValue()));
		case LOGICIMPLIES:
			throw new UnsupportedOperationException(
					"Implications should have been removed during expression normalization.");
		case LOGICIFF:
			throw new UnsupportedOperationException(
					"If and only if expressions should have been removed during expression normalization.");
		case COMPEQ:
			return evaluateCompEq(first, second);
		case COMPNEQ:
			// Don't do anything with the return value here. Just check for inequality and return the
			// appropriate boolean value.
			// TODO it might be necessary to change this behavior for different other abstract domains!
			if (!getSubEvaluator(0).containsBool() && !getSubEvaluator(1).containsBool()) {
				return onlyBoolean(firstValue.isNotEqual(secondValue));
			}
			return onlyTop();
		case COMPGT:
			if (!firstValue.canHandleReals()) {
				mLogger.warnOverapproximatingOperator(mOperator);
			}
			return evaluateCompare(firstValue, secondValue, this::greaterThan, this::greaterThanBool);
		case COMPGEQ:
			return evaluateCompare(firstValue, secondValue, this::greaterOrEqual, this::greaterOrEqualBool);
		case COMPLT:
			if (!firstValue.canHandleReals()) {
				mLogger.warnOverapproximatingOperator(mOperator);
			}
			return evaluateCompare(firstValue, secondValue, this::lessThan, this::lessThanBool);
		case COMPLEQ:
			return evaluateCompare(firstValue, secondValue, this::lessOrEqual, this::lessOrEqualBool);
		case COMPPO:
		default:
			mLogger.warnUnknownOperator(mOperator);
			return onlyTop();
		}
	}

	private Collection<IEvaluationResult<VALUE>> evaluateArithDiv(final IEvaluationResult<VALUE> first,
			final IEvaluationResult<VALUE> second) {
		switch (mEvaluatorType) {
		case INTEGER:
			return onlyValue(first.getValue().divideInteger(second.getValue()));
		case REAL:
			return onlyValue(first.getValue().divideReal(second.getValue()));
		default:
			throw new UnsupportedOperationException("Division on types other than integers and reals is undefined.");
		}
	}

	private Collection<IEvaluationResult<VALUE>> evaluateCompare(final VALUE first, final VALUE second,
			final BiFunction<VALUE, VALUE, VALUE> compareValue,
			final BiFunction<VALUE, VALUE, BooleanValue> compareBoolean) {
		final VALUE returnValue = compareValue.apply(first, second);
		final BooleanValue returnBool;
		if (returnValue.isBottom()) {
			returnBool = BooleanValue.FALSE;
		} else {
			returnBool = compareBoolean.apply(first, second);
		}

		if (!returnBool.isSingleton()) {
			return both(returnValue, returnBool);
		}

		final Collection<IEvaluationResult<VALUE>> rtr = new ArrayList<>();
		rtr.add(new NonrelationalEvaluationResult<>(returnValue, returnBool));
		final BooleanValue negBool = returnBool.neg();
		final Collection<VALUE> compl;
		if (getSubEvaluator(0).getType() == EvaluatorType.INTEGER) {
			compl = returnValue.complementInteger();
		} else {
			compl = returnValue.complement();
		}
		for (final VALUE complement : compl) {
			rtr.add(new NonrelationalEvaluationResult<>(complement, negBool));
		}
		return rtr;
	}

	private Collection<IEvaluationResult<VALUE>> evaluateCompEq(final IEvaluationResult<VALUE> first,
			final IEvaluationResult<VALUE> second) {
		BooleanValue returnBool = BooleanValue.INVALID;
		if (getSubEvaluator(0).containsBool() || getSubEvaluator(1).containsBool()) {
			returnBool = first.getBooleanValue().intersect(second.getBooleanValue()) != BooleanValue.BOTTOM
					? BooleanValue.TRUE
					: BooleanValue.BOTTOM;
		}

		final VALUE returnValue = first.getValue().intersect(second.getValue());

		if (returnBool.isBottom() || returnValue.isBottom()) {
			returnBool = BooleanValue.FALSE;
		} else if (!getSubEvaluator(0).containsBool() && !getSubEvaluator(1).containsBool()) {
			returnBool = first.getValue().isEqual(second.getValue());
		}

		return Collections.singletonList(new NonrelationalEvaluationResult<>(returnValue, returnBool));
	}

	@Override
	public Collection<STATE> inverseEvaluate(final IEvaluationResult<VALUE> evalResult, final STATE oldState) {

		final Collection<STATE> rtr = new HashSet<>();

		final VALUE evalResultValue = evalResult.getValue();
		final BooleanValue evalResultBool = evalResult.getBooleanValue();

		final Collection<IEvaluationResult<VALUE>> leftValues =
				getSubEvaluator(0).evaluate(oldState, getCurrentEvaluationRecursion() + 1);
		final Collection<IEvaluationResult<VALUE>> rightValues =
				getSubEvaluator(1).evaluate(oldState, getCurrentEvaluationRecursion() + 1);

		for (final IEvaluationResult<VALUE> leftOp : leftValues) {
			for (final IEvaluationResult<VALUE> rightOp : rightValues) {
				final VALUE leftOpValue = leftOp.getValue();
				final VALUE rightOpValue = rightOp.getValue();

				// Construct an evaluation result that uses the evaluated value of the sub evaluators, but keeps the
				// overall boolean value of the whole expression (this).
				// This is needed for logical operations to not lose any precision, since in logical evaluation only the
				// boolean value of this expression is important.
				final IEvaluationResult<VALUE> logicalLeftOpValue =
						new NonrelationalEvaluationResult<>(leftOpValue, evalResultBool);
				final IEvaluationResult<VALUE> logicalRightOpValue =
						new NonrelationalEvaluationResult<>(rightOpValue, evalResultBool);

				switch (mOperator) {
				case LOGICAND:
					final Collection<STATE> leftAnd = getSubEvaluator(0).inverseEvaluate(logicalLeftOpValue, oldState,
							getCurrentInverseEvaluationRecursion() + 1);
					final Collection<STATE> rightAnd = getSubEvaluator(1).inverseEvaluate(logicalRightOpValue, oldState,
							getCurrentInverseEvaluationRecursion() + 1);
					rtr.addAll(crossIntersect(leftAnd, rightAnd));
					break;
				case LOGICOR:
					getSubEvaluator(0)
							.inverseEvaluate(logicalLeftOpValue, oldState, getCurrentInverseEvaluationRecursion() + 1)
							.forEach(rtr::add);
					getSubEvaluator(1)
							.inverseEvaluate(logicalRightOpValue, oldState, getCurrentInverseEvaluationRecursion() + 1)
							.forEach(rtr::add);
					break;
				case LOGICIMPLIES:
					throw new UnsupportedOperationException(
							"Implications should have been removed from expressions during expression normalization.");
				case LOGICIFF:
					throw new UnsupportedOperationException(
							"If and only if expressions should have been removed during expression normalization.");
				case COMPEQ:
					final BooleanValue intersectBool = leftOp.getBooleanValue().intersect(rightOp.getBooleanValue());
					if ((getSubEvaluator(0).containsBool() || getSubEvaluator(1).containsBool())
							&& (intersectBool == BooleanValue.TOP)) {
						rtr.add(oldState);
						break;
					}

					final VALUE inverseLeft = inverseEvaluate(evalResultValue, leftOpValue, rightOpValue, true);
					final VALUE inverseRight = inverseEvaluate(evalResultValue, rightOpValue, leftOpValue, false);

					final NonrelationalEvaluationResult<VALUE> leftEvalResult =
							new NonrelationalEvaluationResult<>(inverseLeft, rightOp.getBooleanValue());
					final NonrelationalEvaluationResult<VALUE> rightEvalResult =
							new NonrelationalEvaluationResult<>(inverseRight, leftOp.getBooleanValue());

					final Collection<STATE> leftEq = getSubEvaluator(0).inverseEvaluate(leftEvalResult, oldState,
							getCurrentInverseEvaluationRecursion() + 1);
					final Collection<STATE> rightEq = getSubEvaluator(1).inverseEvaluate(rightEvalResult, oldState,
							getCurrentInverseEvaluationRecursion() + 1);
					rtr.addAll(crossIntersect(leftEq, rightEq));
					break;
				case COMPNEQ:
					if (getSubEvaluator(0).containsBool() || getSubEvaluator(1).containsBool()) {
						throw new UnsupportedOperationException(
								"COMPNEQ operator should not occur for boolean formulas.");
					}
					// If there is a non-boolean formula present, fall through the arithmetic case and evaluate the
					// inequality according to the expected arithmetic values.
				case COMPGT:
				case COMPGEQ:
				case COMPLT:
				case COMPLEQ:
				case ARITHPLUS:
				case ARITHMINUS:
				case ARITHMUL:
				case ARITHDIV:
				case ARITHMOD:
					final VALUE newValueLeft = inverseEvaluate(evalResultValue, leftOpValue, rightOpValue, true);
					final VALUE newValueRight = inverseEvaluate(evalResultValue, rightOpValue, leftOpValue, false);

					final NonrelationalEvaluationResult<VALUE> inverseResultLeft =
							new NonrelationalEvaluationResult<>(newValueLeft, evalResultBool);
					final NonrelationalEvaluationResult<VALUE> inverseResultRight =
							new NonrelationalEvaluationResult<>(newValueRight, evalResultBool);

					final Collection<STATE> leftInverseArith = getSubEvaluator(0).inverseEvaluate(inverseResultLeft,
							oldState, getCurrentInverseEvaluationRecursion() + 1);
					final Collection<STATE> rightInverseArith = getSubEvaluator(1).inverseEvaluate(inverseResultRight,
							oldState, getCurrentInverseEvaluationRecursion() + 1);

					rtr.addAll(crossIntersect(leftInverseArith, rightInverseArith));
					break;
				default:
					mLogger.warnUnknownOperator(mOperator);
					rtr.add(oldState);
					break;
				}

				if (rtr.isEmpty()) {
					rtr.add(oldState);
				}
				// mLogger.logInverseEvaluation(mOperator, returnStates, evalResult, oldState);

			}
		}

		assert !rtr.isEmpty();
		return NonrelationalUtils.mergeStatesIfNecessary(rtr, mMaxParallelSates);
	}

	/**
	 * Intersect all the states of <code>left</code> with all the states of <code>right</code> and return the result.
	 */
	private Collection<STATE> crossIntersect(final Collection<STATE> left, final Collection<STATE> right) {
		final Set<STATE> rtr = new HashSet<>(left.size() * right.size());
		for (final STATE le : left) {
			for (final STATE ri : right) {
				rtr.add(le.intersect(ri));
			}
		}
		return rtr;
	}

	private VALUE inverseEvaluate(final VALUE referenceValue, final VALUE oldValue, final VALUE otherValue,
			final boolean isLeft) {
		VALUE newValue;

		switch (mOperator) {
		case ARITHPLUS:
			newValue = referenceValue.subtract(otherValue);
			newValue = newValue.intersect(oldValue);
			break;
		case ARITHMINUS:
			if (isLeft) {
				newValue = referenceValue.add(otherValue);
			} else {
				newValue = otherValue.subtract(referenceValue);
			}
			newValue = newValue.intersect(oldValue);
			break;
		case ARITHMUL:
			if (mEvaluatorType == EvaluatorType.INTEGER) {
				newValue = referenceValue.divideInteger(otherValue);
			} else if (mEvaluatorType == EvaluatorType.REAL) {
				newValue = referenceValue.divideReal(otherValue);
			} else {
				throw new UnsupportedOperationException(
						"Division on types other than integers and reals is not defined.");
			}
			newValue = newValue.intersect(oldValue);
			break;
		case ARITHDIV:
			if (mEvaluatorType == EvaluatorType.INTEGER) {
				newValue = oldValue;
			} else if (mEvaluatorType == EvaluatorType.REAL) {
				if (isLeft) {
					newValue = referenceValue.multiply(otherValue);
				} else {
					newValue = otherValue.divideReal(referenceValue);
				}
			} else {
				throw new UnsupportedOperationException(
						"Division on types other than integers and reals is not defined.");
			}
			newValue = newValue.intersect(oldValue);
			break;
		case ARITHMOD:
			if (!otherValue.canHandleModulo()) {
				mLogger.warnOverapproximatingOperator(mOperator);
			}
			newValue = otherValue.inverseModulo(referenceValue, oldValue, isLeft);
			break;
		case COMPLEQ:
			newValue = otherValue.inverseLessOrEqual(oldValue, isLeft);
			break;
		case COMPLT:
			if (!otherValue.canHandleReals()) {
				mLogger.warnOverapproximatingOperator(mOperator);
			}
			newValue = otherValue.inverseLessThan(oldValue, isLeft);
			break;
		case COMPGEQ:
			newValue = otherValue.inverseGreaterOrEqual(oldValue, isLeft);
			break;
		case COMPGT:
			if (!otherValue.canHandleReals()) {
				mLogger.warnOverapproximatingOperator(mOperator);
			}
			newValue = otherValue.inverseGreaterThan(oldValue, isLeft);
			break;
		case COMPEQ:
			newValue = otherValue.inverseEquality(oldValue, referenceValue);
			break;
		case COMPNEQ:
			newValue = otherValue.inverseNotEqual(oldValue, referenceValue);
			break;
		default:
			throw new UnsupportedOperationException("Not implemented: " + mOperator);
		}
		return newValue;
	}

	@Override
	public boolean hasFreeOperands() {
		return getNumberOfSubEvaluators() < 2;
	}

	@Override
	public boolean containsBool() {
		return getSubEvaluator(0).containsBool() || getSubEvaluator(1).containsBool();
	}

	@Override
	public void setOperator(final Object operator) {
		assert operator != null;
		assert operator instanceof Operator;

		mOperator = (Operator) operator;
	}

	@Override
	public int getArity() {
		return 2;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();

		sb.append('(').append(getSubEvaluator(0));

		switch (mOperator) {
		case ARITHDIV:
			sb.append(" / ");
			break;
		case ARITHMINUS:
			sb.append(" - ");
			break;
		case ARITHMOD:
			sb.append(" % ");
			break;
		case ARITHMUL:
			sb.append(" * ");
			break;
		case ARITHPLUS:
			sb.append(" + ");
			break;
		case COMPEQ:
			sb.append(" == ");
			break;
		case COMPGEQ:
			sb.append(" >= ");
			break;
		case COMPGT:
			sb.append(" > ");
			break;
		case COMPLEQ:
			sb.append(" <= ");
			break;
		case COMPLT:
			sb.append(" < ");
			break;
		case COMPNEQ:
			sb.append(" != ");
			break;
		case LOGICAND:
			sb.append(" && ");
			break;
		case LOGICIFF:
			sb.append(" <==> ");
			break;
		case LOGICIMPLIES:
			sb.append(" ==> ");
			break;
		case LOGICOR:
			sb.append(" || ");
			break;
		default:
			mOperator.name();
			break;
		}

		sb.append(getSubEvaluator(1)).append(')');

		return sb.toString();
	}

	private Collection<IEvaluationResult<VALUE>> both(final VALUE value, final BooleanValue bvalue) {
		assert value != null;
		assert bvalue != null;
		assert bvalue != BooleanValue.INVALID;
		return Collections.singletonList(new NonrelationalEvaluationResult<>(value, bvalue));
	}

	private Collection<IEvaluationResult<VALUE>> onlyValue(final VALUE value) {
		assert value != null;
		return Collections.singletonList(new NonrelationalEvaluationResult<>(value, BooleanValue.INVALID));
	}

	private Collection<IEvaluationResult<VALUE>> onlyBoolean(final BooleanValue value) {
		assert value != null;
		assert value != BooleanValue.INVALID;
		return Collections.singletonList(new NonrelationalEvaluationResult<>(mTopValue, value));
	}

	private Collection<IEvaluationResult<VALUE>> onlyTop() {
		return Collections.singletonList(new NonrelationalEvaluationResult<>(mTopValue, BooleanValue.TOP));
	}

	private VALUE greaterThan(final VALUE first, final VALUE second) {
		return first.greaterThan(second);
	}

	private VALUE greaterOrEqual(final VALUE first, final VALUE second) {
		return first.greaterOrEqual(second);
	}

	private VALUE lessThan(final VALUE first, final VALUE second) {
		return first.lessThan(second);
	}

	private VALUE lessOrEqual(final VALUE first, final VALUE second) {
		return first.lessOrEqual(second);
	}

	private BooleanValue greaterThanBool(final VALUE first, final VALUE second) {
		return first.isGreaterThan(second);
	}

	private BooleanValue greaterOrEqualBool(final VALUE first, final VALUE second) {
		return first.isGreaterOrEqual(second);
	}

	private BooleanValue lessThanBool(final VALUE first, final VALUE second) {
		return first.isLessThan(second);
	}

	private BooleanValue lessOrEqualBool(final VALUE first, final VALUE second) {
		return first.isLessOrEqual(second);
	}

	@Override
	public EvaluatorType getType() {
		assert getSubEvaluator(0).getType() == getSubEvaluator(1).getType();
		return mEvaluatorType;
	}
}
