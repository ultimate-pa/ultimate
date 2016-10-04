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
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalStateUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

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
public class BinaryExpressionEvaluator<VALUE extends INonrelationalValue<VALUE>, STATE extends INonrelationalAbstractState<STATE, CodeBlock>>
		implements INAryEvaluator<VALUE, STATE, CodeBlock> {

	private final Set<IBoogieVar> mVariableSet;
	private final EvaluatorLogger mLogger;
	private final EvaluatorType mEvaluatorType;
	private final int mMaxParallelSates;

	private final INonrelationalValueFactory<VALUE> mNonrelationalValueFactory;

	private IEvaluator<VALUE, STATE, CodeBlock> mLeftSubEvaluator;
	private IEvaluator<VALUE, STATE, CodeBlock> mRightSubEvaluator;

	private Operator mOperator;

	private final VALUE mTopValue;

	public BinaryExpressionEvaluator(final EvaluatorLogger logger, final EvaluatorType type,
			final int maxParallelStates, final INonrelationalValueFactory<VALUE> nonrelationalValueFactory) {
		mLogger = logger;
		mVariableSet = new HashSet<>();
		mEvaluatorType = type;
		mMaxParallelSates = maxParallelStates;
		mNonrelationalValueFactory = nonrelationalValueFactory;
		mTopValue = mNonrelationalValueFactory.createTopValue();
	}

	@Override
	public List<IEvaluationResult<VALUE>> evaluate(final STATE currentState) {
		assert currentState != null;

		final List<IEvaluationResult<VALUE>> returnList = new ArrayList<>();

		final List<IEvaluationResult<VALUE>> firstResult = mLeftSubEvaluator.evaluate(currentState);
		final List<IEvaluationResult<VALUE>> secondResult = mRightSubEvaluator.evaluate(currentState);

		mLeftSubEvaluator.getVarIdentifiers().forEach(mVariableSet::add);
		mRightSubEvaluator.getVarIdentifiers().forEach(mVariableSet::add);

		final ILogger logger = mLogger.getLogger();
		for (final IEvaluationResult<VALUE> res1 : firstResult) {
			for (final IEvaluationResult<VALUE> res2 : secondResult) {
				final IEvaluationResult<VALUE> result = evaluate(mOperator, res1, res2);
				logger.debug("(" + mOperator + " " + res1 + " " + res2 + ") = " + result);
				returnList.add(result);
			}
		}

		assert !returnList.isEmpty();
		return NonrelationalStateUtils.mergeIfNecessary(returnList, mMaxParallelSates);
	}

	private IEvaluationResult<VALUE> evaluate(final Operator op, final IEvaluationResult<VALUE> first,
			final IEvaluationResult<VALUE> second) {
		switch (op) {
		case ARITHPLUS:
			return onlyValue(first.getValue().add(second.getValue()));
		case ARITHMINUS:
			return onlyValue(first.getValue().subtract(second.getValue()));
		case ARITHMUL:
			return onlyValue(first.getValue().multiply(second.getValue()));
		case ARITHDIV:
			return evaluateArithDiv(first, second);
		case ARITHMOD:
			assert mEvaluatorType == EvaluatorType.INTEGER : "Type error: modulo is not defined on reals";
			return onlyValue(first.getValue().modulo(second.getValue()));
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
			if (!mLeftSubEvaluator.containsBool() && !mRightSubEvaluator.containsBool()) {
				return onlyBoolean(first.getValue().compareInequality(second.getValue()));
			}
			return onlyTop();
		case COMPGT:
			if (!first.getValue().canHandleReals()) {
				mLogger.warnOverapproximatingOperator(mOperator);
			}
			return evaluateCompare(first.getValue(), second.getValue(), (a, b) -> a.greaterThan(b),
					(a, b) -> a.isGreaterThan(b));
		case COMPGEQ:
			return evaluateCompare(first.getValue(), second.getValue(), (a, b) -> a.greaterOrEqual(b),
					(a, b) -> a.isGreaterOrEqual(b));
		case COMPLT:
			if (!first.getValue().canHandleReals()) {
				mLogger.warnOverapproximatingOperator(mOperator);
			}
			return evaluateCompare(first.getValue(), second.getValue(), (a, b) -> a.lessThan(b),
					(a, b) -> a.isLessThan(b));
		case COMPLEQ:
			return evaluateCompare(first.getValue(), second.getValue(), (a, b) -> a.lessOrEqual(b),
					(a, b) -> a.isLessOrEqual(b));
		case COMPPO:
		default:
			mLogger.warnUnknownOperator(mOperator);
			return onlyTop();
		}
	}

	private IEvaluationResult<VALUE> evaluateArithDiv(final IEvaluationResult<VALUE> first,
			final IEvaluationResult<VALUE> second) {
		switch (mEvaluatorType) {
		case INTEGER:
			return onlyValue(first.getValue().divideInteger(second.getValue()));
		case REAL:
			return onlyValue(first.getValue().divide(second.getValue()));
		default:
			throw new UnsupportedOperationException("Division on types other than integers and reals is undefined.");
		}
	}

	private IEvaluationResult<VALUE> evaluateCompare(final VALUE first, final VALUE second,
			final BiFunction<VALUE, VALUE, VALUE> compareValue,
			final BiFunction<VALUE, VALUE, BooleanValue> compareBoolean) {
		final VALUE returnValue = compareValue.apply(first, second);
		final BooleanValue returnBool;
		if (returnValue.isBottom()) {
			returnBool = BooleanValue.FALSE;
		} else {
			returnBool = compareBoolean.apply(first, second);
		}
		return both(returnValue, returnBool);
	}

	private IEvaluationResult<VALUE> evaluateCompEq(final IEvaluationResult<VALUE> first,
			final IEvaluationResult<VALUE> second) {
		BooleanValue returnBool = BooleanValue.INVALID;
		if (mLeftSubEvaluator.containsBool() || mRightSubEvaluator.containsBool()) {
			returnBool = first.getBooleanValue().intersect(second.getBooleanValue()) != BooleanValue.BOTTOM
					? BooleanValue.TRUE : BooleanValue.BOTTOM;
		}

		final VALUE returnValue = first.getValue().intersect(second.getValue());

		if (returnBool.isBottom() || returnValue.isBottom()) {
			returnBool = BooleanValue.FALSE;
		} else if (!mLeftSubEvaluator.containsBool() && !mRightSubEvaluator.containsBool()) {
			returnBool = first.getValue().compareEquality(second.getValue());
		}
		return new NonrelationalEvaluationResult<>(returnValue, returnBool);
	}

	@Override
	public List<STATE> inverseEvaluate(final IEvaluationResult<VALUE> computedValue, final STATE currentState) {

		final List<STATE> returnList = new ArrayList<>();

		final VALUE referenceValue = computedValue.getValue();
		final BooleanValue referenceBool = computedValue.getBooleanValue();

		final List<IEvaluationResult<VALUE>> leftValue = mLeftSubEvaluator.evaluate(currentState);
		final List<IEvaluationResult<VALUE>> rightValue = mRightSubEvaluator.evaluate(currentState);

		for (final IEvaluationResult<VALUE> left : leftValue) {
			for (final IEvaluationResult<VALUE> right : rightValue) {
				final List<STATE> returnStates = new ArrayList<>();

				switch (mOperator) {
				case LOGICAND:
					final List<STATE> leftAnd = mLeftSubEvaluator.inverseEvaluate(computedValue, currentState);
					final List<STATE> rightAnd = mRightSubEvaluator.inverseEvaluate(computedValue, currentState);

					for (final STATE le : leftAnd) {
						for (final STATE ri : rightAnd) {
							returnStates.add(le.intersect(ri));
						}
					}
					break;
				case LOGICOR:
					mLeftSubEvaluator.inverseEvaluate(computedValue, currentState).forEach(returnStates::add);
					mRightSubEvaluator.inverseEvaluate(computedValue, currentState).forEach(returnStates::add);
					break;
				case LOGICIMPLIES:
					throw new UnsupportedOperationException(
							"Implications should have been removed from expressions during expression normalization.");
				case LOGICIFF:
					throw new UnsupportedOperationException(
							"If and only if expressions should have been removed during expression normalization.");
				case COMPEQ:
					final BooleanValue intersectBool = left.getBooleanValue().intersect(right.getBooleanValue());
					if ((mLeftSubEvaluator.containsBool() || mRightSubEvaluator.containsBool())
							&& (intersectBool == BooleanValue.TOP)) {
						returnStates.add(currentState);
						break;
					}

					final VALUE newLeft = computeNewValue(referenceValue, left.getValue(), right.getValue(), true);
					final VALUE newRight = computeNewValue(referenceValue, right.getValue(), left.getValue(), false);

					final NonrelationalEvaluationResult<VALUE> leftEvalresult =
							new NonrelationalEvaluationResult<>(newLeft, right.getBooleanValue());
					final NonrelationalEvaluationResult<VALUE> rightEvalresult =
							new NonrelationalEvaluationResult<>(newRight, left.getBooleanValue());

					final List<STATE> leftEq = mLeftSubEvaluator.inverseEvaluate(leftEvalresult, currentState);
					final List<STATE> rightEq = mRightSubEvaluator.inverseEvaluate(rightEvalresult, currentState);

					for (final STATE le : leftEq) {
						for (final STATE ri : rightEq) {
							returnStates.add(le.intersect(ri));
						}
					}
					break;
				case COMPNEQ:
				case COMPGT:
				case COMPGEQ:
				case COMPLT:
				case COMPLEQ:
				case ARITHPLUS:
				case ARITHMINUS:
				case ARITHMUL:
				case ARITHDIV:
				case ARITHMOD:
					final VALUE newValueLeft = computeNewValue(referenceValue, left.getValue(), right.getValue(), true);
					final VALUE newValueRight =
							computeNewValue(referenceValue, right.getValue(), left.getValue(), false);

					final NonrelationalEvaluationResult<VALUE> inverseResultLeft =
							new NonrelationalEvaluationResult<>(newValueLeft, referenceBool);
					final NonrelationalEvaluationResult<VALUE> inverseResultRight =
							new NonrelationalEvaluationResult<>(newValueRight, referenceBool);

					final List<STATE> leftInverseArith =
							mLeftSubEvaluator.inverseEvaluate(inverseResultLeft, currentState);
					final List<STATE> rightInverseArith =
							mRightSubEvaluator.inverseEvaluate(inverseResultRight, currentState);

					for (final STATE le : leftInverseArith) {
						for (final STATE ri : rightInverseArith) {
							returnStates.add(le.intersect(ri));
						}
					}
					break;
				default:
					mLogger.warnUnknownOperator(mOperator);
					returnStates.add(currentState);
					break;
				}

				if (returnStates.isEmpty()) {
					returnStates.add(currentState);
				}

				returnList.addAll(returnStates);
			}
		}

		assert !returnList.isEmpty();
		return returnList;
	}

	private VALUE computeNewValue(final VALUE referenceValue, final VALUE oldValue, final VALUE otherValue,
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
				newValue = referenceValue.divide(otherValue);
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
					newValue = otherValue.divide(referenceValue);
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
	public void addSubEvaluator(final IEvaluator<VALUE, STATE, CodeBlock> evaluator) {
		assert evaluator != null;

		if (mLeftSubEvaluator != null && mRightSubEvaluator != null) {
			throw new UnsupportedOperationException("There are no free sub evaluators left to be assigned to.");
		}

		if (mLeftSubEvaluator == null) {
			mLeftSubEvaluator = evaluator;
			return;
		}

		mRightSubEvaluator = evaluator;
	}

	@Override
	public Set<IBoogieVar> getVarIdentifiers() {
		return mVariableSet;
	}

	@Override
	public boolean hasFreeOperands() {
		return mLeftSubEvaluator == null || mRightSubEvaluator == null;
	}

	@Override
	public boolean containsBool() {
		return mLeftSubEvaluator.containsBool() || mRightSubEvaluator.containsBool();
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

		sb.append(mLeftSubEvaluator);

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

		sb.append(mRightSubEvaluator);

		return sb.toString();
	}

	private IEvaluationResult<VALUE> both(final VALUE value, final BooleanValue bvalue) {
		assert value != null;
		assert bvalue != null;
		assert bvalue != BooleanValue.INVALID;
		return new NonrelationalEvaluationResult<>(value, bvalue);
	}

	private IEvaluationResult<VALUE> onlyValue(final VALUE value) {
		assert value != null;
		return new NonrelationalEvaluationResult<>(value, BooleanValue.INVALID);
	}

	private IEvaluationResult<VALUE> onlyBoolean(final BooleanValue value) {
		assert value != null;
		assert value != BooleanValue.INVALID;
		return new NonrelationalEvaluationResult<>(mTopValue, value);
	}

	private IEvaluationResult<VALUE> onlyTop() {
		return new NonrelationalEvaluationResult<>(mTopValue, BooleanValue.TOP);
	}

}
