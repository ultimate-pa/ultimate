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

import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue.Value;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class IntervalLogicalBinaryExpressionEvaluator
        implements INAryEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> {

	private IEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> mLeftSubEvaluator;
	private IEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> mRightSubEvaluator;

	private final Set<String> mVariableSet;

	private final Logger mLogger;

	private Operator mOperator;

	private BooleanValue mBooleanValue;

	protected IntervalLogicalBinaryExpressionEvaluator(Logger logger) {
		mLogger = logger;
		mVariableSet = new HashSet<>();
	}

	@Override
	public IEvaluationResult<IntervalDomainEvaluationResult> evaluate(IntervalDomainState currentState) {

		assert currentState != null;

		for (String var : mLeftSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}
		for (String var : mRightSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}

		final IEvaluationResult<IntervalDomainEvaluationResult> firstResult = mLeftSubEvaluator.evaluate(currentState);
		final IEvaluationResult<IntervalDomainEvaluationResult> secondResult = mRightSubEvaluator
		        .evaluate(currentState);

		IntervalDomainState returnState = currentState.copy();
		IntervalDomainValue returnValue = new IntervalDomainValue();

		boolean setToBottom = false;

		switch (mOperator) {
		case ARITHPLUS:
			returnValue = firstResult.getResult().getEvaluatedValue().add(secondResult.getResult().getEvaluatedValue());
			mBooleanValue = new BooleanValue(false);
			break;
		case ARITHMINUS:
			returnValue = firstResult.getResult().getEvaluatedValue()
			        .subtract(secondResult.getResult().getEvaluatedValue());
			mBooleanValue = new BooleanValue(false);
			break;
		case ARITHMUL:
			returnValue = firstResult.getResult().getEvaluatedValue()
			        .multiply(secondResult.getResult().getEvaluatedValue());
			mBooleanValue = new BooleanValue(false);
			break;
		case ARITHMOD:
			returnValue = firstResult.getResult().getEvaluatedValue()
			        .modulus(secondResult.getResult().getEvaluatedValue());
			mBooleanValue = new BooleanValue(false);
			break;
		case LOGICAND:
			mBooleanValue = mLeftSubEvaluator.booleanValue().and(mRightSubEvaluator.booleanValue());
			if (mBooleanValue.getValue() == Value.FALSE) {
				setToBottom = true;
			} else {
				final IntervalDomainState firstIntervalState = firstResult.getResult().getEvaluatedState();
				final IntervalDomainState secondIntervalState = secondResult.getResult().getEvaluatedState();
				returnState = firstIntervalState.intersect(secondIntervalState);
			}
			break;
		case LOGICOR:
			mBooleanValue = mLeftSubEvaluator.booleanValue().or(mRightSubEvaluator.booleanValue());
			if (mBooleanValue.getValue() == Value.FALSE) {
				setToBottom = true;
			}
			break;
		case LOGICIMPLIES:
			mBooleanValue = mLeftSubEvaluator.booleanValue().neg().or(mRightSubEvaluator.booleanValue());
			if (mBooleanValue.getValue() == Value.FALSE) {
				setToBottom = true;
			}
			break;
		case LOGICIFF:
			mBooleanValue = (mLeftSubEvaluator.booleanValue().and(mRightSubEvaluator.booleanValue())
			        .or((mLeftSubEvaluator.booleanValue().neg().and(mRightSubEvaluator.booleanValue().neg()))));
			if (mBooleanValue.getValue() == Value.FALSE) {
				setToBottom = true;
			}
			break;
		case COMPEQ:
			// TODO: Make better, make shorter, move to separate method s.t. it can be called when handling NEQ as well.
			if (mLeftSubEvaluator.getVarIdentifiers().size() == 0
			        && mRightSubEvaluator.getVarIdentifiers().size() == 0) {

				if (mLeftSubEvaluator.containsBool() && mRightSubEvaluator.containsBool()) {
					mBooleanValue = mLeftSubEvaluator.booleanValue().intersect(mRightSubEvaluator.booleanValue());
				} else {
					mBooleanValue = new BooleanValue(firstResult.getResult().getEvaluatedValue()
					        .isEqualTo(secondResult.getResult().getEvaluatedValue()));
				}

				if (mBooleanValue.getValue() == Value.FALSE) {
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
					mBooleanValue = mLeftSubEvaluator.booleanValue().intersect(mRightSubEvaluator.booleanValue());
				} else {
					mBooleanValue = new BooleanValue(firstResult.getResult().getEvaluatedValue()
					        .isEqualTo(secondResult.getResult().getEvaluatedValue()));
				}

				if (mBooleanValue.getValue() == Value.FALSE) {
					setToBottom = true;
				} else {
					if (mLeftSubEvaluator.containsBool()) {
						returnState.setBooleanValue(varName, mLeftSubEvaluator.booleanValue());
					} else {
						returnState.setValue(varName, firstResult.getResult().getEvaluatedValue());
					}

					returnState = returnState.intersect(currentState);
				}

			} else if (mLeftSubEvaluator.getVarIdentifiers().size() == 1
			        && mRightSubEvaluator.getVarIdentifiers().size() == 0) {

				String varName = null;

				for (final String var : mLeftSubEvaluator.getVarIdentifiers()) {
					varName = var;
				}

				assert varName != null;

				if (mLeftSubEvaluator.containsBool() || mRightSubEvaluator.containsBool()) {
					mBooleanValue = mLeftSubEvaluator.booleanValue().intersect(mRightSubEvaluator.booleanValue());
				} else {
					mBooleanValue = new BooleanValue(firstResult.getResult().getEvaluatedValue()
					        .isEqualTo(secondResult.getResult().getEvaluatedValue()));
				}

				if (mBooleanValue.getValue() == Value.FALSE) {
					setToBottom = true;
				} else {
					if (mRightSubEvaluator.containsBool()) {
						returnState.setBooleanValue(varName, mRightSubEvaluator.booleanValue());
					} else {
						returnState.setValue(varName, secondResult.getResult().getEvaluatedValue());
					}

					returnState = returnState.intersect(currentState);
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
					mBooleanValue = mLeftSubEvaluator.booleanValue().intersect(mRightSubEvaluator.booleanValue());
				} else {
					mBooleanValue = new BooleanValue(firstResult.getResult().getEvaluatedValue()
					        .isEqualTo(secondResult.getResult().getEvaluatedValue()));
				}

				if (mBooleanValue.getValue() == Value.FALSE) {
					setToBottom = true;
				} else {
					if (mLeftSubEvaluator.containsBool()) {
						returnState.setBooleanValue(rightVar, mLeftSubEvaluator.booleanValue());
					} else {
						returnState.setValue(rightVar, firstResult.getResult().getEvaluatedValue());
					}

					if (mRightSubEvaluator.containsBool()) {
						returnState.setBooleanValue(leftVar, mRightSubEvaluator.booleanValue());
					} else {
						returnState.setValue(leftVar, secondResult.getResult().getEvaluatedValue());
					}

					returnState = returnState.intersect(currentState);
				}

			} else {
				if (mLeftSubEvaluator.containsBool() && mRightSubEvaluator.containsBool()) {
					mBooleanValue = mLeftSubEvaluator.booleanValue().intersect(mRightSubEvaluator.booleanValue());
				} else {
					mBooleanValue = new BooleanValue(firstResult.getResult().getEvaluatedValue()
					        .isEqualTo(secondResult.getResult().getEvaluatedValue()));
				}
				mLogger.warn(
				        "Cannot handle more than one variables in a sub-tree of an expression. Returning current state.");
			}
			break;
		case COMPNEQ:
			// TODO: Make better, make shorter, move to separate method s.t. it can be called when handling CMPEQ.
			if (mLeftSubEvaluator.getVarIdentifiers().size() == 0
			        && mRightSubEvaluator.getVarIdentifiers().size() == 0) {
				if (mLeftSubEvaluator.containsBool() && mRightSubEvaluator.containsBool()) {
					mBooleanValue = mLeftSubEvaluator.booleanValue().intersect(mRightSubEvaluator.booleanValue()).neg();
				} else {
					mBooleanValue = new BooleanValue(firstResult.getResult().getEvaluatedValue()
					        .isEqualTo(secondResult.getResult().getEvaluatedValue())).neg();
				}

				if (mBooleanValue.getValue() == Value.FALSE) {
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
					mBooleanValue = mLeftSubEvaluator.booleanValue().intersect(mRightSubEvaluator.booleanValue()).neg();
				} else {
					mBooleanValue = new BooleanValue(firstResult.getResult().getEvaluatedValue()
					        .isEqualTo(secondResult.getResult().getEvaluatedValue())).neg();
				}

				if (mBooleanValue.getValue() == Value.FALSE) {
					setToBottom = true;
				} else {
					if (mLeftSubEvaluator.containsBool()) {
						returnState.setBooleanValue(varName, mLeftSubEvaluator.booleanValue().neg());
					} else {
						returnState.setValue(varName, returnState.getValues().get(varName)
						        .intersect(firstResult.getResult().getEvaluatedValue()));
					}

					returnState = returnState.intersect(currentState);
				}
			} else if (mLeftSubEvaluator.getVarIdentifiers().size() == 1
			        && mRightSubEvaluator.getVarIdentifiers().size() == 0) {

				String varName = null;

				for (final String var : mLeftSubEvaluator.getVarIdentifiers()) {
					varName = var;
				}

				assert varName != null;

				if (mLeftSubEvaluator.containsBool() || mRightSubEvaluator.containsBool()) {
					mBooleanValue = mLeftSubEvaluator.booleanValue().intersect(mRightSubEvaluator.booleanValue()).neg();
				} else {
					mBooleanValue = new BooleanValue(firstResult.getResult().getEvaluatedValue()
					        .isEqualTo(secondResult.getResult().getEvaluatedValue())).neg();
				}

				if (mBooleanValue.getValue() == Value.FALSE) {
					setToBottom = true;
				} else {
					if (mRightSubEvaluator.containsBool()) {
						returnState.setBooleanValue(varName, mRightSubEvaluator.booleanValue().neg());
					} else {
						returnState.setValue(varName, returnState.getValues().get(varName)
						        .intersect(secondResult.getResult().getEvaluatedValue()));
					}

					returnState = returnState.intersect(currentState);
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
					mBooleanValue = mLeftSubEvaluator.booleanValue().intersect(mRightSubEvaluator.booleanValue()).neg();
				} else {
					mBooleanValue = new BooleanValue(firstResult.getResult().getEvaluatedValue()
					        .isEqualTo(secondResult.getResult().getEvaluatedValue())).neg();
				}

				if (mBooleanValue.getValue() == Value.FALSE) {
					setToBottom = true;
				} else {
					if (mLeftSubEvaluator.containsBool()) {
						returnState.setBooleanValue(rightVar, mLeftSubEvaluator.booleanValue().neg());
					} else {
						returnState.setValue(rightVar, returnState.getValues().get(rightVar)
						        .intersect(firstResult.getResult().getEvaluatedValue()));
					}

					if (mRightSubEvaluator.containsBool()) {
						returnState.setBooleanValue(leftVar, mRightSubEvaluator.booleanValue().neg());
					} else {
						returnState.setValue(leftVar, returnState.getValues().get(leftVar)
						        .intersect(secondResult.getResult().getEvaluatedValue()));
					}

					returnState = returnState.intersect(currentState);
				}
			} else {
				if (mLeftSubEvaluator.containsBool() && mRightSubEvaluator.containsBool()) {
					mBooleanValue = mLeftSubEvaluator.booleanValue().intersect(mRightSubEvaluator.booleanValue()).neg();
				} else {
					mBooleanValue = new BooleanValue(firstResult.getResult().getEvaluatedValue()
					        .isEqualTo(secondResult.getResult().getEvaluatedValue())).neg();
				}
				mLogger.warn(
				        "Cannot handle more than one variables in a sub-tree of an expression. Returning current state.");
			}
			break;
		case COMPGT:
			mLogger.warn(
			        "Cannot handle greater than operators precisely. Using greater or equal over-approximation instead.");
		case COMPGEQ:
			if (mLeftSubEvaluator.containsBool() || mRightSubEvaluator.containsBool()) {
				throw new UnsupportedOperationException("Boolean values are not allowed in a COMPGEQ expression.");
			}

			if (mLeftSubEvaluator.getVarIdentifiers().size() == 0
			        && mRightSubEvaluator.getVarIdentifiers().size() == 0) {

				if (firstResult.getResult().getEvaluatedValue()
				        .greaterOrEqual(secondResult.getResult().getEvaluatedValue()).isBottom()) {
					mBooleanValue = new BooleanValue(false);
					setToBottom = true;
				} else {
					mBooleanValue = new BooleanValue(true);
				}

			} else if (mLeftSubEvaluator.getVarIdentifiers().size() == 0
			        && mRightSubEvaluator.getVarIdentifiers().size() == 1) {

				String varName = null;

				for (final String var : mRightSubEvaluator.getVarIdentifiers()) {
					varName = var;
				}

				assert varName != null;

				final IntervalDomainValue leftValue = new IntervalDomainValue(new IntervalValue(),
				        firstResult.getResult().getEvaluatedValue().getUpper());

				// final IntervalDomainValue computationResult = firstResult.getResult().getEvaluatedValue()
				// .greaterOrEqual(secondResult.getResult().getEvaluatedValue());
				final IntervalDomainValue computationResult = leftValue
				        .intersect(secondResult.getResult().getEvaluatedValue());

				returnState.setValue(varName, computationResult);

				if (computationResult.isBottom()) {
					mBooleanValue = new BooleanValue(false);
				} else {
					mBooleanValue = new BooleanValue(true);
				}

			} else if (mLeftSubEvaluator.getVarIdentifiers().size() == 1
			        && mRightSubEvaluator.getVarIdentifiers().size() == 0) {

				String varName = null;

				for (final String var : mLeftSubEvaluator.getVarIdentifiers()) {
					varName = var;
				}

				assert varName != null;

				final IntervalDomainValue rightValue = new IntervalDomainValue(
				        secondResult.getResult().getEvaluatedValue().getLower(), new IntervalValue());

				// final IntervalDomainValue computationResult = firstResult.getResult().getEvaluatedValue()
				// .greaterOrEqual(secondResult.getResult().getEvaluatedValue());
				final IntervalDomainValue computationResult = firstResult.getResult().getEvaluatedValue()
				        .intersect(rightValue);

				returnState.setValue(varName, computationResult);

				if (computationResult.isBottom()) {
					mBooleanValue = new BooleanValue(false);
				} else {
					mBooleanValue = new BooleanValue(true);
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

				final IntervalDomainValue rightForLeft = new IntervalDomainValue(
				        secondResult.getResult().getEvaluatedValue().getLower(), new IntervalValue());

				// final IntervalDomainValue leftComputationResult = firstResult.getResult().getEvaluatedValue()
				// .greaterOrEqual(secondResult.getResult().getEvaluatedValue());
				final IntervalDomainValue leftComputationResult = firstResult.getResult().getEvaluatedValue()
				        .intersect(rightForLeft);

				returnState.setValue(leftVar, leftComputationResult);

				final IntervalDomainValue leftForRight = new IntervalDomainValue(new IntervalValue(),
				        firstResult.getResult().getEvaluatedValue().getUpper());
				// final IntervalDomainValue rightComputationResult = firstResult.getResult().getEvaluatedValue()
				// .lessOrEqual(secondResult.getResult().getEvaluatedValue());
				final IntervalDomainValue rightComputationResult = leftForRight
				        .intersect(secondResult.getResult().getEvaluatedValue());
				returnState.setValue(rightVar, rightComputationResult);

				if (leftComputationResult.isBottom() || rightComputationResult.isBottom()) {
					mBooleanValue = new BooleanValue(false);
				} else {
					mBooleanValue = new BooleanValue(true);
				}

			} else {
				if (firstResult.getResult().getEvaluatedValue()
				        .greaterOrEqual(secondResult.getResult().getEvaluatedValue()).isBottom()) {
					mBooleanValue = new BooleanValue(false);
				} else {
					mBooleanValue = new BooleanValue(true);
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
				throw new UnsupportedOperationException("Boolean values are not allowed in a COMPLEQ expression.");
			}

			if (mLeftSubEvaluator.getVarIdentifiers().size() == 0
			        && mRightSubEvaluator.getVarIdentifiers().size() == 0) {

				if (firstResult.getResult().getEvaluatedValue()
				        .lessOrEqual(secondResult.getResult().getEvaluatedValue()).isBottom()) {
					mBooleanValue = new BooleanValue(false);
					setToBottom = true;
				} else {
					mBooleanValue = new BooleanValue(true);
				}
			} else if (mLeftSubEvaluator.getVarIdentifiers().size() == 0
			        && mRightSubEvaluator.getVarIdentifiers().size() == 1) {

				String varName = null;

				for (final String var : mRightSubEvaluator.getVarIdentifiers()) {
					varName = var;
				}

				assert varName != null;

				final IntervalDomainValue newLeftSide = new IntervalDomainValue(
				        firstResult.getResult().getEvaluatedValue().getUpper(), new IntervalValue());

				// final IntervalDomainValue computationResult = firstResult.getResult().getEvaluatedValue()
				// .lessOrEqual(secondResult.getResult().getEvaluatedValue());
				final IntervalDomainValue computationResult = newLeftSide
				        .intersect(secondResult.getResult().getEvaluatedValue());

				returnState.setValue(varName, computationResult);

				if (computationResult.isBottom()) {
					mBooleanValue = new BooleanValue(false);
				} else {
					mBooleanValue = new BooleanValue(true);
				}
			} else if (mLeftSubEvaluator.getVarIdentifiers().size() == 1
			        && mRightSubEvaluator.getVarIdentifiers().size() == 0) {

				String varName = null;

				for (final String var : mLeftSubEvaluator.getVarIdentifiers()) {
					varName = var;
				}

				assert varName != null;

				final IntervalDomainValue newRightSide = new IntervalDomainValue(new IntervalValue(),
				        secondResult.getResult().getEvaluatedValue().getLower());

				// final IntervalDomainValue computationResult = firstResult.getResult().getEvaluatedValue()
				// .lessOrEqual(secondResult.getResult().getEvaluatedValue());
				final IntervalDomainValue computationResult = firstResult.getResult().getEvaluatedValue()
				        .intersect(newRightSide);

				returnState.setValue(varName, computationResult);

				if (computationResult.isBottom()) {
					mBooleanValue = new BooleanValue(false);
				} else {
					mBooleanValue = new BooleanValue(true);
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

				final IntervalDomainValue rightSideForLeft = new IntervalDomainValue(new IntervalValue(),
				        secondResult.getResult().getEvaluatedValue().getLower());
				// final IntervalDomainValue leftComputationResult = firstResult.getResult().getEvaluatedValue()
				// .lessOrEqual(secondResult.getResult().getEvaluatedValue());
				final IntervalDomainValue leftComputationResult = firstResult.getResult().getEvaluatedValue()
				        .intersect(rightSideForLeft);
				returnState.setValue(leftVar, leftComputationResult);

				final IntervalDomainValue leftSideForRight = new IntervalDomainValue(
				        firstResult.getResult().getEvaluatedValue().getUpper(), new IntervalValue());
				// final IntervalDomainValue rightComputationResult = firstResult.getResult().getEvaluatedValue()
				// .greaterOrEqual(secondResult.getResult().getEvaluatedValue());
				final IntervalDomainValue rightComputationResult = leftSideForRight
				        .intersect(secondResult.getResult().getEvaluatedValue());
				returnState.setValue(rightVar, rightComputationResult);

				if (leftComputationResult.isBottom() || rightComputationResult.isBottom()) {
					mBooleanValue = new BooleanValue(false);
				} else {
					mBooleanValue = new BooleanValue(true);
				}
			} else {
				if (firstResult.getResult().getEvaluatedValue()
				        .lessOrEqual(secondResult.getResult().getEvaluatedValue()).isBottom()) {
					mBooleanValue = new BooleanValue(false);
				} else {
					mBooleanValue = new BooleanValue(true);
				}
				mLogger.warn(
				        "Cannot handle more than one variables in a sub-tree of an expression. Returning current state.");
			}
			break;
		case COMPPO:
		default:
			mBooleanValue = new BooleanValue(false);
			mLogger.warn(
			        "Possible loss of precision: cannot handle operator " + mOperator + ". Returning current state.");
			returnValue = new IntervalDomainValue();
		}

		if (setToBottom) {
			returnState.setToBottom();
		}

		return new IntervalDomainEvaluationResult(returnValue, returnState);
	}

	@Override
	public BooleanValue booleanValue() {
		return mBooleanValue;
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
}
