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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.interval;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.BooleanValue.Value;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.EvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.ILogicalEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class IntervalLogicalBinaryExpressionEvaluator extends IntervalBinaryExpressionEvaluator implements
        ILogicalEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>, CodeBlock, IBoogieVar> {

	private BooleanValue mBooleanValue;

	protected IntervalLogicalBinaryExpressionEvaluator(Logger logger) {
		super(logger);
	}

	@Override
	public IEvaluationResult<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>> evaluate(
	        IAbstractState<CodeBlock, IBoogieVar> currentState) {

		assert currentState != null;

		for (String var : mLeftSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}
		for (String var : mRightSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}

		final IEvaluationResult<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>> firstResult = mLeftSubEvaluator
		        .evaluate(currentState);
		final IEvaluationResult<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>> secondResult = mRightSubEvaluator
		        .evaluate(currentState);

		IntervalDomainState returnState = (IntervalDomainState) currentState.copy();
		IntervalDomainValue returnValue = new IntervalDomainValue();

		ILogicalEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>, CodeBlock, IBoogieVar> logicLeft = (ILogicalEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>, CodeBlock, IBoogieVar>) mLeftSubEvaluator;
		ILogicalEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>, CodeBlock, IBoogieVar> logicRight = (ILogicalEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>, CodeBlock, IBoogieVar>) mRightSubEvaluator;

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
		case LOGICAND:
			mBooleanValue = logicLeft.booleanValue().and(logicRight.booleanValue());
			if (mBooleanValue.getValue() == Value.FALSE) {
				setToBottom = true;
			}
			break;
		case LOGICOR:
			mBooleanValue = logicLeft.booleanValue().or(logicRight.booleanValue());
			if (mBooleanValue.getValue() == Value.FALSE) {
				setToBottom = true;
			}
			break;
		case LOGICIMPLIES:
			mBooleanValue = logicLeft.booleanValue().neg().or(logicRight.booleanValue());
			if (mBooleanValue.getValue() == Value.FALSE) {
				setToBottom = true;
			}
			break;
		case LOGICIFF:
			mBooleanValue = (logicLeft.booleanValue().and(logicRight.booleanValue())
			        .or((logicLeft.booleanValue().neg().and(logicRight.booleanValue().neg()))));
			if (mBooleanValue.getValue() == Value.FALSE) {
				setToBottom = true;
			}
			break;
		case COMPEQ:
			// TODO: Make better, make shorter, move to separate method s.t. it can be called when handling NEQ as well.
			if (mLeftSubEvaluator.getVarIdentifiers().size() == 0
			        && mRightSubEvaluator.getVarIdentifiers().size() == 0) {

				if (logicLeft.containsBool() && logicRight.containsBool()) {
					mBooleanValue = new BooleanValue(logicLeft.booleanValue().equals(logicRight.booleanValue()));
				} else {
					mBooleanValue = new BooleanValue(firstResult.getResult().getEvaluatedValue()
					        .equals(secondResult.getResult().getEvaluatedValue()));
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

				if (logicLeft.containsBool() || logicRight.containsBool()) {
					mBooleanValue = new BooleanValue(logicLeft.booleanValue().equals(logicRight.booleanValue()));
				} else {
					mBooleanValue = new BooleanValue(firstResult.getResult().getEvaluatedValue()
					        .equals(secondResult.getResult().getEvaluatedValue()));
				}

				if (mBooleanValue.getValue() == Value.FALSE) {
					setToBottom = true;
				} else {
					if (logicLeft.containsBool()) {
						returnState.setBooleanValue(varName, logicLeft.booleanValue());
					} else {
						returnState.setValue(varName, firstResult.getResult().getEvaluatedValue());
					}

					returnState = (IntervalDomainState) returnState.intersect((IntervalDomainState) currentState);
				}

			} else if (mLeftSubEvaluator.getVarIdentifiers().size() == 1
			        && mRightSubEvaluator.getVarIdentifiers().size() == 0) {

				String varName = null;

				for (final String var : mLeftSubEvaluator.getVarIdentifiers()) {
					varName = var;
				}

				assert varName != null;

				if (logicLeft.containsBool() || logicRight.containsBool()) {
					mBooleanValue = new BooleanValue(logicLeft.booleanValue().equals(logicRight.booleanValue()));
				} else {
					mBooleanValue = new BooleanValue(firstResult.getResult().getEvaluatedValue()
					        .equals(secondResult.getResult().getEvaluatedValue()));
				}

				if (mBooleanValue.getValue() == Value.FALSE) {
					setToBottom = true;
				} else {
					if (logicRight.containsBool()) {
						returnState.setBooleanValue(varName, logicRight.booleanValue());
					} else {
						returnState.setValue(varName, secondResult.getResult().getEvaluatedValue());
					}

					returnState = (IntervalDomainState) returnState.intersect((IntervalDomainState) currentState);
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

				if (logicLeft.containsBool() || logicRight.containsBool()) {
					mBooleanValue = new BooleanValue(logicLeft.booleanValue().equals(logicRight.booleanValue()));
				} else {
					mBooleanValue = new BooleanValue(firstResult.getResult().getEvaluatedValue()
					        .equals(secondResult.getResult().getEvaluatedValue()));
				}

				if (mBooleanValue.getValue() == Value.FALSE) {
					setToBottom = true;
				} else {
					if (logicLeft.containsBool()) {
						returnState.setBooleanValue(rightVar, logicLeft.booleanValue());
					} else {
						returnState.setValue(rightVar, firstResult.getResult().getEvaluatedValue());
					}

					if (logicRight.containsBool()) {
						returnState.setBooleanValue(leftVar, logicRight.booleanValue());
					} else {
						returnState.setValue(leftVar, secondResult.getResult().getEvaluatedValue());
					}

					returnState = (IntervalDomainState) returnState.intersect((IntervalDomainState) currentState);
				}

			} else {
				if (logicLeft.containsBool() && logicRight.containsBool()) {
					mBooleanValue = new BooleanValue(logicLeft.booleanValue().equals(logicRight.booleanValue()));
				} else {
					mBooleanValue = new BooleanValue(firstResult.getResult().getEvaluatedValue()
					        .equals(secondResult.getResult().getEvaluatedValue()));
				}
				mLogger.warn(
				        "Cannot handle more than one variables in a sub-tree of an expression. Returning current state.");
			}
			break;
		case COMPNEQ:
			// TODO: Make better, make shorter, move to separate method s.t. it can be called when handling CMPEQ.
			if (mLeftSubEvaluator.getVarIdentifiers().size() == 0
			        && mRightSubEvaluator.getVarIdentifiers().size() == 0) {
				if (logicLeft.containsBool() && logicRight.containsBool()) {
					mBooleanValue = new BooleanValue(logicLeft.booleanValue().equals(logicRight.booleanValue())).neg();
				} else {
					mBooleanValue = new BooleanValue(firstResult.getResult().getEvaluatedValue()
					        .equals(secondResult.getResult().getEvaluatedValue())).neg();
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

				if (logicLeft.containsBool() || logicRight.containsBool()) {
					mBooleanValue = new BooleanValue(logicLeft.booleanValue().equals(logicRight.booleanValue())).neg();
				} else {
					mBooleanValue = new BooleanValue(firstResult.getResult().getEvaluatedValue()
					        .equals(secondResult.getResult().getEvaluatedValue())).neg();
				}

				if (mBooleanValue.getValue() == Value.FALSE) {
					setToBottom = true;
				} else {
					if (logicLeft.containsBool()) {
						returnState.setBooleanValue(varName, logicLeft.booleanValue().neg());
					} else {
						returnState.setValue(varName, returnState.getValues().get(varName)
						        .intersect(firstResult.getResult().getEvaluatedValue()));
					}

					returnState = (IntervalDomainState) returnState.intersect((IntervalDomainState) currentState);
				}
			} else if (mLeftSubEvaluator.getVarIdentifiers().size() == 1
			        && mRightSubEvaluator.getVarIdentifiers().size() == 0) {

				String varName = null;

				for (final String var : mLeftSubEvaluator.getVarIdentifiers()) {
					varName = var;
				}

				assert varName != null;

				if (logicLeft.containsBool() || logicRight.containsBool()) {
					mBooleanValue = new BooleanValue(logicLeft.booleanValue().equals(logicRight.booleanValue())).neg();
				} else {
					mBooleanValue = new BooleanValue(firstResult.getResult().getEvaluatedValue()
					        .equals(secondResult.getResult().getEvaluatedValue())).neg();
				}

				if (mBooleanValue.getValue() == Value.FALSE) {
					setToBottom = true;
				} else {
					if (logicRight.containsBool()) {
						returnState.setBooleanValue(varName, logicRight.booleanValue().neg());
					} else {
						returnState.setValue(varName, returnState.getValues().get(varName)
						        .intersect(secondResult.getResult().getEvaluatedValue()));
					}

					returnState = (IntervalDomainState) returnState.intersect((IntervalDomainState) currentState);
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

				if (logicLeft.containsBool() || logicRight.containsBool()) {
					mBooleanValue = new BooleanValue(logicLeft.booleanValue().equals(logicRight.booleanValue())).neg();
				} else {
					mBooleanValue = new BooleanValue(firstResult.getResult().getEvaluatedValue()
					        .equals(secondResult.getResult().getEvaluatedValue())).neg();
				}

				if (mBooleanValue.getValue() == Value.FALSE) {
					setToBottom = true;
				} else {
					if (logicLeft.containsBool()) {
						returnState.setBooleanValue(rightVar, logicLeft.booleanValue().neg());
					} else {
						returnState.setValue(rightVar, returnState.getValues().get(rightVar)
						        .intersect(firstResult.getResult().getEvaluatedValue()));
					}

					if (logicRight.containsBool()) {
						returnState.setBooleanValue(leftVar, logicRight.booleanValue().neg());
					} else {
						returnState.setValue(leftVar, returnState.getValues().get(leftVar)
						        .intersect(secondResult.getResult().getEvaluatedValue()));
					}

					returnState = (IntervalDomainState) returnState.intersect((IntervalDomainState) currentState);
				}
			} else {
				if (logicLeft.containsBool() && logicRight.containsBool()) {
					mBooleanValue = new BooleanValue(logicLeft.booleanValue().equals(logicRight.booleanValue())).neg();
				} else {
					mBooleanValue = new BooleanValue(firstResult.getResult().getEvaluatedValue()
					        .equals(secondResult.getResult().getEvaluatedValue())).neg();
				}
				mLogger.warn(
				        "Cannot handle more than one variables in a sub-tree of an expression. Returning current state.");
			}
			break;
		case COMPGT:
			mLogger.warn(
			        "Cannot handle greater than operations precisely. Using greater or equal over-approximation instead.");
		case COMPGEQ:
			if (logicLeft.containsBool() || logicRight.containsBool()) {
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

				final IntervalDomainValue computationResult = firstResult.getResult().getEvaluatedValue()
				        .greaterOrEqual(secondResult.getResult().getEvaluatedValue());

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

				final IntervalDomainValue computationResult = firstResult.getResult().getEvaluatedValue()
				        .greaterOrEqual(secondResult.getResult().getEvaluatedValue());

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

				final IntervalDomainValue leftComputationResult = firstResult.getResult().getEvaluatedValue()
				        .greaterOrEqual(secondResult.getResult().getEvaluatedValue());
				returnState.setValue(leftVar, leftComputationResult);

				final IntervalDomainValue rightComputationResult = firstResult.getResult().getEvaluatedValue()
				        .lessOrEqual(secondResult.getResult().getEvaluatedValue());
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
			        "Cannot handle less than operations precisely. Using less or equal over-approximation instead.");
		case COMPLEQ:
			if (logicLeft.containsBool() || logicRight.containsBool()) {
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

				final IntervalDomainValue computationResult = firstResult.getResult().getEvaluatedValue()
				        .lessOrEqual(secondResult.getResult().getEvaluatedValue());

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

				final IntervalDomainValue computationResult = firstResult.getResult().getEvaluatedValue()
				        .lessOrEqual(secondResult.getResult().getEvaluatedValue());

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

				final IntervalDomainValue leftComputationResult = firstResult.getResult().getEvaluatedValue()
				        .lessOrEqual(secondResult.getResult().getEvaluatedValue());
				returnState.setValue(leftVar, leftComputationResult);

				final IntervalDomainValue rightComputationResult = firstResult.getResult().getEvaluatedValue()
				        .greaterOrEqual(secondResult.getResult().getEvaluatedValue());
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

		return new EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>(returnValue, returnState);
	}

	@Override
	public BooleanValue booleanValue() {
		return mBooleanValue;
	}

	@Override
	public boolean containsBool() {
		final ILogicalEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>, CodeBlock, IBoogieVar> logicLeft = (ILogicalEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>, CodeBlock, IBoogieVar>) mLeftSubEvaluator;
		final ILogicalEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>, CodeBlock, IBoogieVar> logicRight = (ILogicalEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>, CodeBlock, IBoogieVar>) mRightSubEvaluator;
		return logicLeft.containsBool() || logicRight.containsBool();
	}
}
