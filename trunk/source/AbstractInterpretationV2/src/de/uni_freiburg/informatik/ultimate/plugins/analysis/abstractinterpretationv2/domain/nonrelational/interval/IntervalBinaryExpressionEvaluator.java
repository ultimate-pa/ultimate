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
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class IntervalBinaryExpressionEvaluator
        implements INAryEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> {

	private final Set<String> mVariableSet;
	private final Logger mLogger;
	private final EvaluatorType mEvaluatorType;
	private final int mMaxParallelStates;

	private IEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> mLeftSubEvaluator;
	private IEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> mRightSubEvaluator;

	private Operator mOperator;

	protected IntervalBinaryExpressionEvaluator(final Logger logger, final EvaluatorType type) {
		mLogger = logger;
		mVariableSet = new HashSet<>();
		mEvaluatorType = type;
		mMaxParallelStates = new UltimatePreferenceStore(Activator.PLUGIN_ID)
		        .getInt(AbsIntPrefInitializer.LABEL_STATES_UNTIL_MERGE);
	}

	@Override
	public List<IEvaluationResult<IntervalDomainEvaluationResult>> evaluate(IntervalDomainState currentState) {

		final List<IEvaluationResult<IntervalDomainEvaluationResult>> returnList = new ArrayList<>();

		assert currentState != null;

		final List<IEvaluationResult<IntervalDomainEvaluationResult>> firstResult = mergeIfNecessary(
				mLeftSubEvaluator.evaluate(currentState));
		final List<IEvaluationResult<IntervalDomainEvaluationResult>> secondResult = mergeIfNecessary(
				mRightSubEvaluator.evaluate(currentState));

		for (String var : mLeftSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}
		for (String var : mRightSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}

		for (final IEvaluationResult<IntervalDomainEvaluationResult> res1 : firstResult) {
			for (final IEvaluationResult<IntervalDomainEvaluationResult> res2 : secondResult) {
				final List<IntervalDomainState> returnStates = new ArrayList<>();
				IntervalDomainValue returnValue = new IntervalDomainValue();
				BooleanValue returnBool = new BooleanValue();

				switch (mOperator) {
				case ARITHPLUS:
					returnValue = res1.getResult().getEvaluatedValue().add(res2.getResult().getEvaluatedValue());
					returnBool = new BooleanValue(false);
					break;
				case ARITHMINUS:
					returnValue = res1.getResult().getEvaluatedValue().subtract(res2.getResult().getEvaluatedValue());
					returnBool = new BooleanValue(false);
					break;
				case ARITHMUL:
					returnValue = res1.getResult().getEvaluatedValue().multiply(res2.getResult().getEvaluatedValue());
					returnBool = new BooleanValue(false);
					break;
				case ARITHDIV:
					switch (mEvaluatorType) {
					case INTEGER:
						returnValue = res1.getResult().getEvaluatedValue()
								.integerDivide(res2.getResult().getEvaluatedValue());
						break;
					case REAL:
						returnValue = res1.getResult().getEvaluatedValue().divide(res2.getResult().getEvaluatedValue());
						break;
					default:
						throw new UnsupportedOperationException(
								"Division on types other than integers and reals is undefined.");
					}
					returnBool = new BooleanValue(false);
					break;
				case ARITHMOD:
					mLogger.warn("Cannot handle modulo operation precisely. Returning top.");
					// returnValue = res1.getResult().getEvaluatedValue().modulo(res2.getResult().getEvaluatedValue());
					returnBool = new BooleanValue(false);
					break;
				case LOGICAND:
					returnBool = res1.getBooleanValue().and(res2.getBooleanValue());
					final IntervalDomainState firstIntervalStateAnd = res1.getResult().getEvaluatedState();
					final IntervalDomainState secondIntervalStateAnd = res2.getResult().getEvaluatedState();
					returnStates.add(firstIntervalStateAnd.intersect(secondIntervalStateAnd));
					break;
				case LOGICOR:
					returnBool = res1.getBooleanValue().or(res2.getBooleanValue());
					final IntervalDomainState firstIntervalStateOr = res1.getResult().getEvaluatedState();
					final IntervalDomainState secondIntervalStateOr = res2.getResult().getEvaluatedState();

					returnStates.add(firstIntervalStateOr);
					returnStates.add(secondIntervalStateOr);
					break;
				case LOGICIMPLIES:
					throw new UnsupportedOperationException("Implications should have been resolved earlier.");
				case LOGICIFF:
					throw new UnsupportedOperationException(
							"If and only if expressions should have been resolved earlier.");
				case COMPEQ:
					BooleanValue booleanValue = new BooleanValue();
					IntervalDomainValue intervalValue = new IntervalDomainValue();

					if (mLeftSubEvaluator.containsBool() || mRightSubEvaluator.containsBool()) {
						booleanValue = res1.getBooleanValue().intersect(res2.getBooleanValue());
					}

					intervalValue = res1.getResult().getEvaluatedValue()
					        .intersect(res2.getResult().getEvaluatedValue());

					if (booleanValue.isBottom() || intervalValue.isBottom()) {
						returnBool = new BooleanValue(false);
						returnStates.add(currentState.bottomState());
						break;
					} else {
						returnBool = new BooleanValue(true);
					}

					final IntervalDomainEvaluationResult inverseResult = new IntervalDomainEvaluationResult(
					        intervalValue, currentState, booleanValue);

					final List<IEvaluationResult<IntervalDomainEvaluationResult>> leftInverse = mLeftSubEvaluator
					        .inverseEvaluate(inverseResult);
					final List<IEvaluationResult<IntervalDomainEvaluationResult>> rightInverse = mRightSubEvaluator
					        .inverseEvaluate(inverseResult);

					for (final IEvaluationResult<IntervalDomainEvaluationResult> left : leftInverse) {
						for (final IEvaluationResult<IntervalDomainEvaluationResult> right : rightInverse) {
							final IntervalDomainState intersect = left.getResult().getEvaluatedState()
							        .intersect(right.getResult().getEvaluatedState());
							if (!intersect.isBottom()) {
								returnStates.add(intersect);
							}
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
					final IntervalDomainValue intervalValueGeq = res1.getResult().getEvaluatedValue()
					        .greaterOrEqual(res2.getResult().getEvaluatedValue());

					if (intervalValueGeq.isBottom()) {
						returnBool = new BooleanValue(false);
						returnStates.add(currentState.bottomState());
						break;
					} else {
						returnBool = new BooleanValue(true);
					}

					final IntervalDomainValue rightForLeftGeq = new IntervalDomainValue(
					        res2.getResult().getEvaluatedValue().getLower(), new IntervalValue());
					final IntervalDomainValue leftComputationResultGeq = res1.getResult().getEvaluatedValue()
					        .intersect(rightForLeftGeq);

					final IntervalDomainValue leftForRightGeq = new IntervalDomainValue(new IntervalValue(),
					        res1.getResult().getEvaluatedValue().getUpper());
					final IntervalDomainValue rightComputationResultGeq = res2.getResult().getEvaluatedValue()
					        .intersect(leftForRightGeq);

					final IntervalDomainEvaluationResult inverseResultGeqLeft = new IntervalDomainEvaluationResult(
					        leftComputationResultGeq, currentState, returnBool);
					final IntervalDomainEvaluationResult inverseResultGeqRight = new IntervalDomainEvaluationResult(
					        rightComputationResultGeq, currentState, returnBool);

					final List<IEvaluationResult<IntervalDomainEvaluationResult>> leftInverseGeq = mLeftSubEvaluator
					        .inverseEvaluate(inverseResultGeqLeft);
					final List<IEvaluationResult<IntervalDomainEvaluationResult>> rightInverseGeq = mRightSubEvaluator
					        .inverseEvaluate(inverseResultGeqRight);

					for (final IEvaluationResult<IntervalDomainEvaluationResult> left : leftInverseGeq) {
						for (final IEvaluationResult<IntervalDomainEvaluationResult> right : rightInverseGeq) {
							returnStates.add(left.getResult().getEvaluatedState()
							        .intersect(right.getResult().getEvaluatedState()));
						}
					}
					break;
				case COMPLT:
					mLogger.warn(
							"Cannot handle less than operators precisely. Using less or equal over-approximation instead.");
				case COMPLEQ:
					final IntervalDomainValue intervalValueLeq = res1.getResult().getEvaluatedValue()
					        .lessOrEqual(res2.getResult().getEvaluatedValue());

					if (intervalValueLeq.isBottom()) {
						returnBool = new BooleanValue(false);
						returnStates.add(currentState.bottomState());
						break;
					} else {
						returnBool = new BooleanValue(true);
					}

					final IntervalDomainValue rightForLeftLeq = new IntervalDomainValue(new IntervalValue(),
					        res2.getResult().getEvaluatedValue().getUpper());
					final IntervalDomainValue leftComputationResultLeq = res1.getResult().getEvaluatedValue()
					        .intersect(rightForLeftLeq);

					final IntervalDomainValue leftForRightLeq = new IntervalDomainValue(
					        res1.getResult().getEvaluatedValue().getLower(), new IntervalValue());
					final IntervalDomainValue rightComputationResultLeq = res2.getResult().getEvaluatedValue()
					        .intersect(leftForRightLeq);

					final IntervalDomainEvaluationResult inverseResultLeqLeft = new IntervalDomainEvaluationResult(
					        leftComputationResultLeq, currentState, returnBool);
					final IntervalDomainEvaluationResult inverseResultLeqRight = new IntervalDomainEvaluationResult(
					        rightComputationResultLeq, currentState, returnBool);

					final List<IEvaluationResult<IntervalDomainEvaluationResult>> leftInverseLeq = mLeftSubEvaluator
					        .inverseEvaluate(inverseResultLeqLeft);
					final List<IEvaluationResult<IntervalDomainEvaluationResult>> rightInverseLeq = mRightSubEvaluator
					        .inverseEvaluate(inverseResultLeqRight);

					for (final IEvaluationResult<IntervalDomainEvaluationResult> left : leftInverseLeq) {
						for (final IEvaluationResult<IntervalDomainEvaluationResult> right : rightInverseLeq) {
							returnStates.add(left.getResult().getEvaluatedState()
							        .intersect(right.getResult().getEvaluatedState()));
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

				// If no state has been added to return, return the current state.
				if (returnStates.size() == 0) {
					returnStates.add(currentState.copy());
				}

				for (final IntervalDomainState s : returnStates) {
					if (s.isBottom()) {
						returnList.add(new IntervalDomainEvaluationResult(returnValue, s, new BooleanValue(false)));
					} else {
						returnList.add(new IntervalDomainEvaluationResult(returnValue, s, returnBool));
					}

				}
			}
		}

		assert returnList.size() != 0;
		return returnList;
	}

	private List<IEvaluationResult<IntervalDomainEvaluationResult>> mergeIfNecessary(
	        final List<IEvaluationResult<IntervalDomainEvaluationResult>> results) {
		if (results.size() > mMaxParallelStates) {
			return Collections.singletonList(results.stream().reduce(this::merge).get());
		}
		return results;
	}

	private IEvaluationResult<IntervalDomainEvaluationResult> merge(
	        final IEvaluationResult<IntervalDomainEvaluationResult> a,
	        final IEvaluationResult<IntervalDomainEvaluationResult> b) {
		final IntervalDomainEvaluationResult left = a.getResult();
		final IntervalDomainEvaluationResult right = b.getResult();
		return new IntervalDomainEvaluationResult(left.getEvaluatedValue().merge(right.getEvaluatedValue()),
		        left.getEvaluatedState().merge(right.getEvaluatedState()),
		        left.getBooleanValue().merge(right.getBooleanValue()));
	}

	@Override
	public boolean containsBool() {
		return mLeftSubEvaluator.containsBool() || mRightSubEvaluator.containsBool();
	}

	@Override
	public void addSubEvaluator(
	        IEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> evaluator) {
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
	public void setOperator(Object operator) {
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
	public List<IEvaluationResult<IntervalDomainEvaluationResult>> inverseEvaluate(
	        IEvaluationResult<IntervalDomainEvaluationResult> computedState) {

		final List<IEvaluationResult<IntervalDomainEvaluationResult>> returnList = new ArrayList<>();

		final IntervalDomainValue referenceValue = computedState.getResult().getEvaluatedValue();

		final BooleanValue oldBooleanValue = computedState.getBooleanValue();
		final IntervalDomainState oldState = computedState.getResult().getEvaluatedState();

		final List<IEvaluationResult<IntervalDomainEvaluationResult>> leftValue = mLeftSubEvaluator.evaluate(oldState);
		final List<IEvaluationResult<IntervalDomainEvaluationResult>> rightValue = mRightSubEvaluator
		        .evaluate(oldState);

		for (final IEvaluationResult<IntervalDomainEvaluationResult> left : leftValue) {
			for (final IEvaluationResult<IntervalDomainEvaluationResult> right : rightValue) {
				final IntervalDomainValue newLeft = computeNewValue(referenceValue,
				        left.getResult().getEvaluatedValue(), right.getResult().getEvaluatedValue(), true);
				final IntervalDomainValue newRight = computeNewValue(referenceValue,
				        right.getResult().getEvaluatedValue(), left.getResult().getEvaluatedValue(), false);

				final IntervalDomainEvaluationResult leftEvalresult = new IntervalDomainEvaluationResult(newLeft,
				        oldState, oldBooleanValue);
				final IntervalDomainEvaluationResult rightEvalresult = new IntervalDomainEvaluationResult(newRight,
				        oldState, oldBooleanValue);
				final List<IEvaluationResult<IntervalDomainEvaluationResult>> leftInverse = mLeftSubEvaluator
				        .inverseEvaluate(leftEvalresult);
				final List<IEvaluationResult<IntervalDomainEvaluationResult>> rightInverse = mRightSubEvaluator
				        .inverseEvaluate(rightEvalresult);

				for (final IEvaluationResult<IntervalDomainEvaluationResult> le : leftInverse) {
					for (final IEvaluationResult<IntervalDomainEvaluationResult> re : rightInverse) {
						final IntervalDomainEvaluationResult realResult = new IntervalDomainEvaluationResult(
						        referenceValue,
						        le.getResult().getEvaluatedState().intersect(re.getResult().getEvaluatedState()),
						        oldBooleanValue);

						returnList.add(realResult);
					}
				}
			}
		}

		assert returnList.size() != 0;
		return returnList;
	}

	private IntervalDomainValue computeNewValue(final IntervalDomainValue referenceValue,
	        final IntervalDomainValue oldValue, final IntervalDomainValue otherValue, boolean left) {
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
			mLogger.warn("Cannot handle inverse of the modulo operation precisely. Returning old value.");
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
