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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue.Value;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class IntervalBinaryExpressionEvaluator
        implements INAryEvaluator<IntervalDomainValue, IntervalDomainState, CodeBlock, IBoogieVar> {

	private final Set<String> mVariableSet;
	private final ILogger mLogger;
	private final EvaluatorType mEvaluatorType;
	private final int mMaxParallelStates;

	private IEvaluator<IntervalDomainValue, IntervalDomainState, CodeBlock, IBoogieVar> mLeftSubEvaluator;
	private IEvaluator<IntervalDomainValue, IntervalDomainState, CodeBlock, IBoogieVar> mRightSubEvaluator;

	private Operator mOperator;

	protected IntervalBinaryExpressionEvaluator(final ILogger logger, final EvaluatorType type) {
		mLogger = logger;
		mVariableSet = new HashSet<>();
		mEvaluatorType = type;
		mMaxParallelStates = new UltimatePreferenceStore(Activator.PLUGIN_ID)
		        .getInt(AbsIntPrefInitializer.LABEL_MAX_PARALLEL_STATES);
	}

	@Override
	public List<IEvaluationResult<IntervalDomainValue>> evaluate(final IntervalDomainState currentState) {

		final List<IEvaluationResult<IntervalDomainValue>> returnList = new ArrayList<>();

		assert currentState != null;

		final List<IEvaluationResult<IntervalDomainValue>> firstResult = mLeftSubEvaluator.evaluate(currentState);
		final List<IEvaluationResult<IntervalDomainValue>> secondResult = mRightSubEvaluator.evaluate(currentState);

		for (final String var : mLeftSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}
		for (final String var : mRightSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}

		for (final IEvaluationResult<IntervalDomainValue> res1 : firstResult) {
			for (final IEvaluationResult<IntervalDomainValue> res2 : secondResult) {
				IntervalDomainValue returnValue = new IntervalDomainValue();
				BooleanValue returnBool = new BooleanValue();

				switch (mOperator) {
				case ARITHPLUS:
					returnValue = res1.getValue().add(res2.getValue());
					returnBool = new BooleanValue(false);
					break;
				case ARITHMINUS:
					returnValue = res1.getValue().subtract(res2.getValue());
					returnBool = new BooleanValue(false);
					break;
				case ARITHMUL:
					returnValue = res1.getValue().multiply(res2.getValue());
					returnBool = new BooleanValue(false);
					break;
				case ARITHDIV:
					switch (mEvaluatorType) {
					case INTEGER:
						returnValue = res1.getValue().integerDivide(res2.getValue());
						break;
					case REAL:
						returnValue = res1.getValue().divide(res2.getValue());
						break;
					default:
						throw new UnsupportedOperationException(
						        "Division on types other than integers and reals is undefined.");
					}
					returnBool = new BooleanValue(false);
					break;
				case ARITHMOD:
					switch (mEvaluatorType) {
					case INTEGER:
						returnValue = res1.getValue().modulo(res2.getValue(), true);
						break;
					case REAL:
						returnValue = res1.getValue().modulo(res2.getValue(), false);
						break;
					default:
						throw new UnsupportedOperationException(
						        "Modulo operation on types other than integers and reals is undefined.");
					}
					returnBool = new BooleanValue(false);
					break;
				case LOGICAND:
					returnBool = res1.getBooleanValue().and(res2.getBooleanValue());
					break;
				case LOGICOR:
					returnBool = res1.getBooleanValue().or(res2.getBooleanValue());
					break;
				case LOGICIMPLIES:
					throw new UnsupportedOperationException("Implications should have been resolved earlier.");
				case LOGICIFF:
					throw new UnsupportedOperationException(
					        "If and only if expressions should have been resolved earlier.");
				case COMPEQ:
					if (mLeftSubEvaluator.containsBool() || mRightSubEvaluator.containsBool()) {
						returnBool = res1.getBooleanValue().intersect(res2.getBooleanValue());
						if (returnBool.getValue() != Value.BOTTOM) {
							returnBool = new BooleanValue(true);
						}
					}

					returnValue = res1.getValue().intersect(res2.getValue());

					if (returnBool.isBottom() || returnValue.isBottom()) {
						returnBool = new BooleanValue(false);
						break;
					}

					if (!mLeftSubEvaluator.containsBool() && !mRightSubEvaluator.containsBool()) {
						if (returnValue.isEqualTo(res1.getValue()) && returnValue.isEqualTo(res2.getValue())) {
							returnBool = new BooleanValue(true);
						} else {
							returnBool = new BooleanValue();
						}
					}
					break;
				case COMPNEQ:
					throw new UnsupportedOperationException(
					        "COMPNEQ expression occurs even though it should have been replaced before.");
				case COMPGT:
					mLogger.warn(
					        "Cannot handle greater than operators precisely. Using greater or equal over-approximation instead.");
				case COMPGEQ:
					returnValue = res1.getValue().greaterOrEqual(res2.getValue());

					if (returnValue.isBottom()) {
						returnBool = new BooleanValue(false);
						break;
					} else {
						final IntervalDomainValue leq = res1.getValue().lessOrEqual(res2.getValue());
						if (leq.isBottom() || leq.isPointInterval()) {
							returnBool = new BooleanValue(true);
						} else {
							returnBool = new BooleanValue();
						}
					}
					break;
				case COMPLT:
					mLogger.warn(
					        "Cannot handle less than operators precisely. Using less or equal over-approximation instead.");
				case COMPLEQ:
					returnValue = res1.getValue().lessOrEqual(res2.getValue());

					if (returnValue.isBottom()) {
						returnBool = new BooleanValue(false);
						break;
					} else {
						final IntervalDomainValue geq = res1.getValue().greaterOrEqual(res2.getValue());
						if (geq.isBottom() || geq.isPointInterval()) {
							returnBool = new BooleanValue(true);
						} else {
							returnBool = new BooleanValue();
						}
					}
					break;
				case COMPPO:
				default:
					returnBool = new BooleanValue(false);
					mLogger.warn("Possible loss of precision: cannot handle operator " + mOperator
					        + ". Returning current state.");
					returnValue = new IntervalDomainValue();
				}
				returnList.add(new IntervalDomainEvaluationResult(returnValue, returnBool));
			}
		}

		assert !returnList.isEmpty();
		return IntervalUtils.mergeIfNecessary(returnList, mMaxParallelStates);

	}

	@Override
	public boolean containsBool() {
		return mLeftSubEvaluator.containsBool() || mRightSubEvaluator.containsBool();
	}

	@Override
	public void addSubEvaluator(
	        final IEvaluator<IntervalDomainValue, IntervalDomainState, CodeBlock, IBoogieVar> evaluator) {
		assert evaluator != null;

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
		}

		sb.append(mRightSubEvaluator);

		return sb.toString();
	}

	@Override
	public List<IntervalDomainState> inverseEvaluate(final IEvaluationResult<IntervalDomainValue> computedValue,
	        final IntervalDomainState currentState) {

		final List<IntervalDomainState> returnList = new ArrayList<>();

		final IntervalDomainValue referenceValue = computedValue.getValue();
		final BooleanValue referenceBool = computedValue.getBooleanValue();

		final List<IEvaluationResult<IntervalDomainValue>> leftValue = mLeftSubEvaluator.evaluate(currentState);
		final List<IEvaluationResult<IntervalDomainValue>> rightValue = mRightSubEvaluator.evaluate(currentState);

		for (final IEvaluationResult<IntervalDomainValue> left : leftValue) {
			for (final IEvaluationResult<IntervalDomainValue> right : rightValue) {
				final List<IntervalDomainState> returnStates = new ArrayList<>();

				switch (mOperator) {
				case LOGICAND:
					final List<IntervalDomainState> leftAnd = mLeftSubEvaluator.inverseEvaluate(computedValue,
					        currentState);
					final List<IntervalDomainState> rightAnd = mRightSubEvaluator.inverseEvaluate(computedValue,
					        currentState);
					for (final IntervalDomainState le : leftAnd) {
						for (final IntervalDomainState ri : rightAnd) {
							returnStates.add(le.intersect(ri));
						}
					}
					break;
				case LOGICOR:
					final List<IntervalDomainState> leftOr = mLeftSubEvaluator.inverseEvaluate(computedValue,
					        currentState);
					final List<IntervalDomainState> rightOr = mRightSubEvaluator.inverseEvaluate(computedValue,
					        currentState);
					for (final IntervalDomainState le : leftOr) {
						returnStates.add(le);
					}
					for (final IntervalDomainState ri : rightOr) {
						returnStates.add(ri);
					}
					break;
				case LOGICIMPLIES:
					throw new UnsupportedOperationException("Implications should have been resolved earlier.");
				case LOGICIFF:
					throw new UnsupportedOperationException(
					        "If and only if expressions should have been resolved earlier.");
				case COMPEQ:
					final BooleanValue intersectBool = left.getBooleanValue().intersect(right.getBooleanValue());
					if ((mLeftSubEvaluator.containsBool() || mRightSubEvaluator.containsBool())
					        && (intersectBool.getValue() == Value.TOP)) {
						returnStates.add(currentState);
						break;
					}

					final IntervalDomainValue newLeft = computeNewValue(referenceValue, left.getValue(),
					        right.getValue(), true);
					final IntervalDomainValue newRight = computeNewValue(referenceValue, right.getValue(),
					        left.getValue(), false);

					final IntervalDomainEvaluationResult leftEvalresult = new IntervalDomainEvaluationResult(newLeft,
					        right.getBooleanValue());
					final IntervalDomainEvaluationResult rightEvalresult = new IntervalDomainEvaluationResult(newRight,
					        left.getBooleanValue());

					final List<IntervalDomainState> leftEq = mLeftSubEvaluator.inverseEvaluate(leftEvalresult,
					        currentState);
					final List<IntervalDomainState> rightEq = mRightSubEvaluator.inverseEvaluate(rightEvalresult,
					        currentState);
					for (final IntervalDomainState le : leftEq) {
						for (final IntervalDomainState ri : rightEq) {
							returnStates.add(le.intersect(ri));
						}
					}
					break;
				case COMPNEQ:
					throw new UnsupportedOperationException(
					        "COMPNEQ expression occurs even though it should have been replaced before.");
				case COMPGT:
					mLogger.warn(
					        "Cannot handle greater than operators precisely. Using greater or equal over-approximation instead.");
				case COMPGEQ:
					// Construct interval of the form [lower, \infty) for the right hand side.
					final IntervalDomainValue rightForLeftGeq = new IntervalDomainValue(right.getValue().getLower(),
					        new IntervalValue());
					final IntervalDomainValue leftComputationResultGeq = left.getValue().intersect(rightForLeftGeq);

					// Construct interval of the form (-\infty, upper] for the left hand side.
					final IntervalDomainValue leftForRightGeq = new IntervalDomainValue(new IntervalValue(),
					        left.getValue().getUpper());
					final IntervalDomainValue rightComputationResultGeq = right.getValue().intersect(leftForRightGeq);

					// Prepare reference evaluation results for the inverse evaluation.
					final IntervalDomainEvaluationResult inverseResultGeqLeft = new IntervalDomainEvaluationResult(
					        leftComputationResultGeq, left.getBooleanValue());
					final IntervalDomainEvaluationResult inverseResultGeqRight = new IntervalDomainEvaluationResult(
					        rightComputationResultGeq, right.getBooleanValue());

					// Inverse evaluate.
					final List<IntervalDomainState> leftInverseGeq = mLeftSubEvaluator
					        .inverseEvaluate(inverseResultGeqLeft, currentState);
					final List<IntervalDomainState> rightInverseGeq = mRightSubEvaluator
					        .inverseEvaluate(inverseResultGeqRight, currentState);

					for (final IntervalDomainState le : leftInverseGeq) {
						for (final IntervalDomainState ri : rightInverseGeq) {
							returnStates.add(le.intersect(ri));
						}
					}
					break;
				case COMPLT:
					mLogger.warn(
					        "Cannot handle less than operators precisely. Using less or equal over-approximation instead.");
				case COMPLEQ:
					// Construct interval of the form (-\infty, upper] for the right hand side.
					final IntervalDomainValue rightForLeftLeq = new IntervalDomainValue(new IntervalValue(),
					        right.getValue().getUpper());
					final IntervalDomainValue leftComputationResultLeq = left.getValue().intersect(rightForLeftLeq);

					// Construct interval of the form [lower, \infty) for the left hand side.
					final IntervalDomainValue leftForRightLeq = new IntervalDomainValue(left.getValue().getLower(),
					        new IntervalValue());
					final IntervalDomainValue rightComputationResultLeq = right.getValue().intersect(leftForRightLeq);

					// Prepare reference evaluation result for the invere evaluation.
					final IntervalDomainEvaluationResult inverseResultLeqLeft = new IntervalDomainEvaluationResult(
					        leftComputationResultLeq, left.getBooleanValue());
					final IntervalDomainEvaluationResult inverseResultLeqRight = new IntervalDomainEvaluationResult(
					        rightComputationResultLeq, right.getBooleanValue());

					// Inverse evaluate.
					final List<IntervalDomainState> leftInverseLeq = mLeftSubEvaluator
					        .inverseEvaluate(inverseResultLeqLeft, currentState);
					final List<IntervalDomainState> rightInverseLeq = mRightSubEvaluator
					        .inverseEvaluate(inverseResultLeqRight, currentState);

					for (final IntervalDomainState le : leftInverseLeq) {
						for (final IntervalDomainState ri : rightInverseLeq) {
							returnStates.add(le.intersect(ri));
						}
					}
					break;
				case COMPPO:
					returnStates.add(currentState);
					break;
				case ARITHDIV:
				case ARITHMINUS:
				case ARITHMOD:
				case ARITHMUL:
				case ARITHPLUS:
					final IntervalDomainValue newArithValueLeft = computeNewValue(referenceValue, left.getValue(),
					        right.getValue(), true);
					final IntervalDomainValue newArithValueRight = computeNewValue(referenceValue, right.getValue(),
					        left.getValue(), false);

					final IntervalDomainEvaluationResult inverseResultArithLeft = new IntervalDomainEvaluationResult(
					        newArithValueLeft, referenceBool);
					final IntervalDomainEvaluationResult inverseResultArithRight = new IntervalDomainEvaluationResult(
					        newArithValueRight, referenceBool);

					final List<IntervalDomainState> leftInverseArith = mLeftSubEvaluator
					        .inverseEvaluate(inverseResultArithLeft, currentState);
					final List<IntervalDomainState> rightInverseArith = mRightSubEvaluator
					        .inverseEvaluate(inverseResultArithRight, currentState);

					for (final IntervalDomainState le : leftInverseArith) {
						for (final IntervalDomainState ri : rightInverseArith) {
							returnStates.add(le.intersect(ri));
						}
					}
					break;
				default:
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

	private IntervalDomainValue computeNewValue(final IntervalDomainValue referenceValue,
	        final IntervalDomainValue oldValue, final IntervalDomainValue otherValue, final boolean left) {
		IntervalDomainValue newValue;

		switch (mOperator) {
		case ARITHPLUS:
			newValue = referenceValue.subtract(otherValue);
			newValue = newValue.intersect(oldValue);
			break;
		case ARITHMINUS:
			if (left) {
				newValue = referenceValue.add(otherValue);
			} else {
				newValue = otherValue.subtract(referenceValue);
			}
			newValue = newValue.intersect(oldValue);
			break;
		case ARITHMUL:
			if (mEvaluatorType == EvaluatorType.INTEGER) {
				newValue = referenceValue.integerDivide(otherValue);
			} else if (mEvaluatorType == EvaluatorType.REAL) {
				newValue = referenceValue.divide(otherValue);
			} else {
				throw new UnsupportedOperationException(
				        "Division on types other than integers and reals is undefined.");
			}
			newValue = newValue.intersect(oldValue);
			break;
		case ARITHDIV:
			if (left) {
				newValue = referenceValue.multiply(otherValue);
			} else {
				if (mEvaluatorType == EvaluatorType.INTEGER) {
					newValue = otherValue.integerDivide(referenceValue);
				} else if (mEvaluatorType == EvaluatorType.REAL) {
					newValue = otherValue.divide(referenceValue);
				} else {
					throw new UnsupportedOperationException(
					        "Division on types other than integers and reals is undefined.");
				}
			}
			newValue = newValue.intersect(oldValue);
			break;
		case ARITHMOD:
			mLogger.debug("Cannot handle inverse of the modulo operation precisely. Returning old value.");
			newValue = oldValue;
			break;
		case COMPEQ:
		case COMPLEQ:
		case COMPLT:
		case COMPGEQ:
		case COMPGT:
		case COMPNEQ:
			newValue = referenceValue;
			break;
		default:
			throw new UnsupportedOperationException("Not implemented: " + mOperator);
		}
		return newValue;
	}
}
