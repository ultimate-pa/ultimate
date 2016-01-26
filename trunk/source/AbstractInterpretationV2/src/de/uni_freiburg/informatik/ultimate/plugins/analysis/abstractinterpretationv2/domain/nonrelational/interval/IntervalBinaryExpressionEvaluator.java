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

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue.Value;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class IntervalBinaryExpressionEvaluator
        implements INAryEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> {

	private final Set<String> mVariableSet;
	private final Logger mLogger;
	private final EvaluatorType mEvaluatorType;

	private IEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> mLeftSubEvaluator;
	private IEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> mRightSubEvaluator;

	private Operator mOperator;

	protected IntervalBinaryExpressionEvaluator(Logger logger, EvaluatorType type) {
		mLogger = logger;
		mVariableSet = new HashSet<>();
		mEvaluatorType = type;
	}

	@Override
	public List<IEvaluationResult<IntervalDomainEvaluationResult>> evaluate(IntervalDomainState currentState) {

		final List<IEvaluationResult<IntervalDomainEvaluationResult>> returnList = new ArrayList<>();

		assert currentState != null;

		final List<IEvaluationResult<IntervalDomainEvaluationResult>> firstResult = mLeftSubEvaluator
		        .evaluate(currentState);
		final List<IEvaluationResult<IntervalDomainEvaluationResult>> secondResult = mRightSubEvaluator
		        .evaluate(currentState);

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

				boolean setToBottom = false;

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
					returnValue = res1.getResult().getEvaluatedValue().modulo(res2.getResult().getEvaluatedValue());
					returnBool = new BooleanValue(false);
					break;
				case LOGICAND:
					returnBool = res1.getBooleanValue().and(res2.getBooleanValue());
					if (returnBool.getValue() == Value.FALSE) {
						setToBottom = true;
					} else {
						final IntervalDomainState firstIntervalState = res1.getResult().getEvaluatedState();
						final IntervalDomainState secondIntervalState = res2.getResult().getEvaluatedState();
						returnStates.add(firstIntervalState.intersect(secondIntervalState));
					}
					break;
				case LOGICOR:
					returnBool = res1.getBooleanValue().or(res2.getBooleanValue());
					if (returnBool.getValue() == Value.FALSE) {
						setToBottom = true;
					} else {
						final IntervalDomainState firstIntervalState = res1.getResult().getEvaluatedState();
						final IntervalDomainState secondIntervalState = res2.getResult().getEvaluatedState();

						returnStates.add(firstIntervalState);
						returnStates.add(secondIntervalState);
					}
					break;
				case LOGICIMPLIES:
					returnBool = res1.getBooleanValue().neg().or(res2.getBooleanValue());
					if (returnBool.getValue() == Value.FALSE) {
						setToBottom = true;
					}
					// TODO: Do something with the state here!
					break;
				case LOGICIFF:
					returnBool = (res1.getBooleanValue().and(res2.getBooleanValue())
					        .or((res1.getBooleanValue().neg().and(res2.getBooleanValue().neg()))));
					if (returnBool.getValue() == Value.FALSE) {
						setToBottom = true;
					}
					// TODO: Do something with the state here!
					break;
				case COMPEQ:
					// TODO: Make better, make shorter, move to separate method s.t. it can be called when handling NEQ
					// as well.
					if (mLeftSubEvaluator.getVarIdentifiers().size() == 0
					        && mRightSubEvaluator.getVarIdentifiers().size() == 0) {

						if (mLeftSubEvaluator.containsBool() && mRightSubEvaluator.containsBool()) {
							returnBool = res1.getBooleanValue().intersect(res2.getBooleanValue());
						} else {
							returnBool = new BooleanValue(res1.getResult().getEvaluatedValue()
							        .isContainedIn(res2.getResult().getEvaluatedValue()));
						}

						if (returnBool.getValue() == Value.FALSE) {
							setToBottom = true;
						}

					} else if (mLeftSubEvaluator.getVarIdentifiers().size() == 0
					        && mRightSubEvaluator.getVarIdentifiers().size() == 1) {

						String varName = null;

						for (final String var : mRightSubEvaluator.getVarIdentifiers()) {
							varName = var;
						}

						assert varName != null;

						if (mLeftSubEvaluator.containsBool() || mRightSubEvaluator.containsBool()) {
							returnBool = res1.getBooleanValue().intersect(res2.getBooleanValue());
						} else {
							returnBool = new BooleanValue(res1.getResult().getEvaluatedValue()
							        .isContainedIn(res2.getResult().getEvaluatedValue()));
						}

						if (returnBool.getValue() == Value.FALSE) {
							setToBottom = true;
						} else {
							IntervalDomainState returnState;

							if (mLeftSubEvaluator.containsBool()) {
								returnState = currentState.setBooleanValue(varName, res1.getBooleanValue());
							} else {
								returnState = currentState.setValue(varName, res1.getResult().getEvaluatedValue());
							}

							returnStates.add(returnState.intersect(currentState));
						}

					} else if (mLeftSubEvaluator.getVarIdentifiers().size() == 1
					        && mRightSubEvaluator.getVarIdentifiers().size() == 0) {

						String varName = null;

						for (final String var : mLeftSubEvaluator.getVarIdentifiers()) {
							varName = var;
						}

						assert varName != null;

						if (mLeftSubEvaluator.containsBool() || mRightSubEvaluator.containsBool()) {
							returnBool = res1.getBooleanValue().intersect(res2.getBooleanValue());
						} else {
							returnBool = new BooleanValue(res1.getResult().getEvaluatedValue()
							        .isContainedIn(res2.getResult().getEvaluatedValue()));
						}

						if (returnBool.getValue() == Value.FALSE) {
							setToBottom = true;
						} else {
							IntervalDomainState returnState;

							if (mRightSubEvaluator.containsBool()) {
								returnState = currentState.setBooleanValue(varName, res2.getBooleanValue());
							} else {
								returnState = currentState.setValue(varName, res2.getResult().getEvaluatedValue());
							}

							returnStates.add(returnState.intersect(currentState));
						}

					} else if (mLeftSubEvaluator.getVarIdentifiers().size() == 1
					        && mRightSubEvaluator.getVarIdentifiers().size() == 1) {

						String leftVar = null;
						String rightVar = null;

						for (final String var : mLeftSubEvaluator.getVarIdentifiers()) {
							leftVar = var;
						}
						for (final String var : mRightSubEvaluator.getVarIdentifiers()) {
							rightVar = var;
						}

						assert leftVar != null;
						assert rightVar != null;

						if (mLeftSubEvaluator.containsBool() || mRightSubEvaluator.containsBool()) {
							returnBool = res1.getBooleanValue().intersect(res2.getBooleanValue());
						} else {
							returnBool = new BooleanValue(res1.getResult().getEvaluatedValue()
							        .isContainedIn(res2.getResult().getEvaluatedValue()));
						}

						if (returnBool.getValue() == Value.FALSE) {
							setToBottom = true;
						} else {
							List<String> boolVarsToChange = new ArrayList<>();
							List<String> varsToChange = new ArrayList<>();
							List<BooleanValue.Value> boolsToChange = new ArrayList<>();
							List<IntervalDomainValue> valsToChange = new ArrayList<>();

							if (mLeftSubEvaluator.containsBool()) {
								boolVarsToChange.add(rightVar);
								boolsToChange.add(res1.getBooleanValue().getValue());
							} else {
								varsToChange.add(rightVar);
								valsToChange.add(res1.getResult().getEvaluatedValue());
							}

							if (mRightSubEvaluator.containsBool()) {
								boolVarsToChange.add(leftVar);
								boolsToChange.add(res2.getBooleanValue().getValue());
							} else {
								varsToChange.add(leftVar);
								valsToChange.add(res2.getResult().getEvaluatedValue());
							}

							returnStates.add(
							        currentState.setMixedValues(varsToChange.toArray(new String[varsToChange.size()]),
							                valsToChange.toArray(new IntervalDomainValue[valsToChange.size()]),
							                boolVarsToChange.toArray(new String[boolVarsToChange.size()]),
							                boolsToChange.toArray(new BooleanValue.Value[boolsToChange.size()]),
							                new String[0], new IntervalDomainValue[0]).intersect(currentState));
						}

					} else {
						if (mLeftSubEvaluator.containsBool() && mRightSubEvaluator.containsBool()) {
							returnBool = res1.getBooleanValue().intersect(res2.getBooleanValue());
						} else {
							returnBool = new BooleanValue(res1.getResult().getEvaluatedValue()
							        .isContainedIn(res2.getResult().getEvaluatedValue()));
						}

						if (returnBool.getValue() == Value.FALSE) {
							setToBottom = true;
						}

						mLogger.warn(
						        "Cannot handle more than one variables in a sub-tree of an expression. Returning current state.");
					}
					break;
				case COMPNEQ:
					throw new UnsupportedOperationException(
					        "COMPNEQ expression occurs even though it should have been replaced before.");
				case COMPGT:
					mLogger.warn(
					        "Cannot handle greater than operators precisely. Using greater or equal over-approximation instead.");
				case COMPGEQ:
					if (mLeftSubEvaluator.containsBool() || mRightSubEvaluator.containsBool()) {
						throw new UnsupportedOperationException(
						        "Boolean values are not allowed in a COMPGEQ expression.");
					}

					if (mLeftSubEvaluator.getVarIdentifiers().size() == 0
					        && mRightSubEvaluator.getVarIdentifiers().size() == 0) {

						if (res1.getResult().getEvaluatedValue().greaterOrEqual(res2.getResult().getEvaluatedValue())
						        .isBottom()) {
							returnBool = new BooleanValue(false);
							setToBottom = true;
						} else {
							returnBool = new BooleanValue(true);
						}

					} else if (mLeftSubEvaluator.getVarIdentifiers().size() == 0
					        && mRightSubEvaluator.getVarIdentifiers().size() == 1) {

						String varName = null;

						for (final String var : mRightSubEvaluator.getVarIdentifiers()) {
							varName = var;
						}

						assert varName != null;

						final IntervalDomainValue leftValue = new IntervalDomainValue(new IntervalValue(),
						        res1.getResult().getEvaluatedValue().getUpper());

						final IntervalDomainValue computationResult = leftValue
						        .intersect(res2.getResult().getEvaluatedValue());

						returnStates.add(currentState.setValue(varName, computationResult));

						if (computationResult.isBottom()) {
							returnBool = new BooleanValue(false);
						} else {
							returnBool = new BooleanValue(true);
						}

					} else if (mLeftSubEvaluator.getVarIdentifiers().size() == 1
					        && mRightSubEvaluator.getVarIdentifiers().size() == 0) {

						String varName = null;

						for (final String var : mLeftSubEvaluator.getVarIdentifiers()) {
							varName = var;
						}

						assert varName != null;

						final IntervalDomainValue rightValue = new IntervalDomainValue(
						        res2.getResult().getEvaluatedValue().getLower(), new IntervalValue());

						final IntervalDomainValue computationResult = res1.getResult().getEvaluatedValue()
						        .intersect(rightValue);

						returnStates.add(currentState.setValue(varName, computationResult));

						if (computationResult.isBottom()) {
							returnBool = new BooleanValue(false);
						} else {
							returnBool = new BooleanValue(true);
						}

					} else if (mLeftSubEvaluator.getVarIdentifiers().size() == 1
					        && mRightSubEvaluator.getVarIdentifiers().size() == 1) {

						String leftVar = null;
						String rightVar = null;

						for (final String var : mLeftSubEvaluator.getVarIdentifiers()) {
							leftVar = var;
						}
						for (final String var : mRightSubEvaluator.getVarIdentifiers()) {
							rightVar = var;
						}

						assert leftVar != null;
						assert rightVar != null;

						List<String> vars = new ArrayList<>();
						List<IntervalDomainValue> vals = new ArrayList<>();

						final IntervalDomainValue rightForLeft = new IntervalDomainValue(
						        res2.getResult().getEvaluatedValue().getLower(), new IntervalValue());

						final IntervalDomainValue leftComputationResult = res1.getResult().getEvaluatedValue()
						        .intersect(rightForLeft);

						vars.add(leftVar);
						vals.add(leftComputationResult);

						final IntervalDomainValue leftForRight = new IntervalDomainValue(new IntervalValue(),
						        res1.getResult().getEvaluatedValue().getUpper());

						final IntervalDomainValue rightComputationResult = leftForRight
						        .intersect(res2.getResult().getEvaluatedValue());

						vars.add(rightVar);
						vals.add(rightComputationResult);

						returnStates.add(currentState.setValues(vars.toArray(new String[vars.size()]),
						        vals.toArray(new IntervalDomainValue[vals.size()])));

						if (leftComputationResult.isBottom() || rightComputationResult.isBottom()) {
							returnBool = new BooleanValue(false);
						} else {
							returnBool = new BooleanValue(true);
						}

					} else {
						if (res1.getResult().getEvaluatedValue().greaterOrEqual(res2.getResult().getEvaluatedValue())
						        .isBottom()) {
							returnBool = new BooleanValue(false);
						} else {
							returnBool = new BooleanValue(true);
						}
						mLogger.warn(
						        "Cannot handle more than one variables in a sub-tree of an expression. Returning current state.");
					}
					break;
				case COMPLT:
					mLogger.warn(
					        "Cannot handle less than operators precisely. Using less or equal over-approximation instead.");
				case COMPLEQ:
					if (mLeftSubEvaluator.containsBool() || mRightSubEvaluator.containsBool()) {
						throw new UnsupportedOperationException(
						        "Boolean values are not allowed in a COMPLEQ expression.");
					}

					if (mLeftSubEvaluator.getVarIdentifiers().size() == 0
					        && mRightSubEvaluator.getVarIdentifiers().size() == 0) {

						if (res1.getResult().getEvaluatedValue().lessOrEqual(res2.getResult().getEvaluatedValue())
						        .isBottom()) {
							returnBool = new BooleanValue(false);
							setToBottom = true;
						} else {
							returnBool = new BooleanValue(true);
						}
					} else if (mLeftSubEvaluator.getVarIdentifiers().size() == 0
					        && mRightSubEvaluator.getVarIdentifiers().size() == 1) {

						String varName = null;

						for (final String var : mRightSubEvaluator.getVarIdentifiers()) {
							varName = var;
						}

						assert varName != null;

						final IntervalDomainValue newLeftSide = new IntervalDomainValue(
						        res1.getResult().getEvaluatedValue().getUpper(), new IntervalValue());

						final IntervalDomainValue computationResult = newLeftSide
						        .intersect(res2.getResult().getEvaluatedValue());

						returnStates.add(currentState.setValue(varName, computationResult));

						if (computationResult.isBottom()) {
							returnBool = new BooleanValue(false);
						} else {
							returnBool = new BooleanValue(true);
						}
					} else if (mLeftSubEvaluator.getVarIdentifiers().size() == 1
					        && mRightSubEvaluator.getVarIdentifiers().size() == 0) {

						String varName = null;

						for (final String var : mLeftSubEvaluator.getVarIdentifiers()) {
							varName = var;
						}

						assert varName != null;

						final IntervalDomainValue newRightSide = new IntervalDomainValue(new IntervalValue(),
						        res2.getResult().getEvaluatedValue().getLower());

						final IntervalDomainValue computationResult = res1.getResult().getEvaluatedValue()
						        .intersect(newRightSide);

						returnStates.add(currentState.setValue(varName, computationResult));

						if (computationResult.isBottom()) {
							returnBool = new BooleanValue(false);
						} else {
							returnBool = new BooleanValue(true);
						}
					} else if (mLeftSubEvaluator.getVarIdentifiers().size() == 1
					        && mRightSubEvaluator.getVarIdentifiers().size() == 1) {

						String leftVar = null;
						String rightVar = null;

						for (final String var : mLeftSubEvaluator.getVarIdentifiers()) {
							leftVar = var;
						}
						for (final String var : mRightSubEvaluator.getVarIdentifiers()) {
							rightVar = var;
						}

						assert leftVar != null;
						assert rightVar != null;

						List<String> vars = new ArrayList<>();
						List<IntervalDomainValue> vals = new ArrayList<>();

						final IntervalDomainValue rightSideForLeft = new IntervalDomainValue(new IntervalValue(),
						        res2.getResult().getEvaluatedValue().getLower());

						final IntervalDomainValue leftComputationResult = res1.getResult().getEvaluatedValue()
						        .intersect(rightSideForLeft);

						vars.add(leftVar);
						vals.add(leftComputationResult);

						final IntervalDomainValue leftSideForRight = new IntervalDomainValue(
						        res1.getResult().getEvaluatedValue().getUpper(), new IntervalValue());

						final IntervalDomainValue rightComputationResult = leftSideForRight
						        .intersect(res2.getResult().getEvaluatedValue());

						vars.add(rightVar);
						vals.add(rightComputationResult);

						returnStates.add(currentState.setValues(vars.toArray(new String[vars.size()]),
						        vals.toArray(new IntervalDomainValue[vals.size()])));

						if (leftComputationResult.isBottom() || rightComputationResult.isBottom()) {
							returnBool = new BooleanValue(false);
						} else {
							returnBool = new BooleanValue(true);
						}
					} else {
						if (res1.getResult().getEvaluatedValue().lessOrEqual(res2.getResult().getEvaluatedValue())
						        .isBottom()) {
							returnBool = new BooleanValue(false);
						} else {
							returnBool = new BooleanValue(true);
						}
						mLogger.warn(
						        "Cannot handle more than one variables in a sub-tree of an expression. Returning current state.");
					}
					break;
				case COMPPO:
				default:
					returnBool = new BooleanValue(false);
					mLogger.warn("Possible loss of precision: cannot handle operator " + mOperator
					        + ". Returning current state.");
					returnValue = new IntervalDomainValue();
				}

				if (setToBottom) {
					returnStates.clear();
					returnStates.add(currentState.bottomState());
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

		return returnList;
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
	public EvaluatorType getEvaluatorType() {

		return null;
	}
}
