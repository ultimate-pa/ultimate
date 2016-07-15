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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign.SignDomainValue.SignValues;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class SignLogicalBinaryExpressionEvaluator extends SignBinaryExpressionEvaluator
		implements IEvaluator<SignDomainValue, SignDomainState, CodeBlock> {

	private final BooleanValue mBooleanValue = new BooleanValue(false);

	public SignLogicalBinaryExpressionEvaluator(ILogger logger, EvaluatorType type) {
		super(logger, type);
	}

	@Override
	public List<IEvaluationResult<SignDomainValue>> evaluate(SignDomainState currentState) {
		final List<IEvaluationResult<SignDomainValue>> returnList = new ArrayList<>();

		for (final IBoogieVar var : mLeftSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}
		for (final IBoogieVar var : mRightSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}

		final List<IEvaluationResult<SignDomainValue>> firstResult = mLeftSubEvaluator.evaluate(currentState);
		final List<IEvaluationResult<SignDomainValue>> secondResult = mRightSubEvaluator.evaluate(currentState);

		for (final IEvaluationResult<SignDomainValue> res1 : firstResult) {
			for (final IEvaluationResult<SignDomainValue> res2 : secondResult) {
				switch (mOperator) {
				// case LOGICIFF:
				// break;
				// case LOGICIMPLIES:
				// break;
				// case LOGICAND:
				// break;
				// case LOGICOR:
				// break;
				// case COMPLT:
				// break;
				// case COMPGT:
				// break;
				// case COMPLEQ:
				// break;
				// case COMPGEQ:
				// break;
				case COMPEQ:
				case COMPNEQ:
					// return evaluateComparisonOperators(firstResult, secondResult);
					// case COMPPO:
					// break;
					// case BITVECCONCAT:
					// break;
					// case ARITHMUL:
					// break;
					// case ARITHDIV:
					// break;
					// case ARITHMOD:
					// break;
					// case ARITHPLUS:
					// break;
					// case ARITHMINUS:
					// break;
				default:
					throw new UnsupportedOperationException(
							"The operator " + mOperator.toString() + " is not implemented.");
				}
			}
		}

		return returnList;
	}

	private SignDomainState logicallyInterpret(SignDomainState currentState) {

		final SignDomainValue firstResult = (SignDomainValue) mLeftSubEvaluator.evaluate(currentState);
		final SignDomainValue secondResult = (SignDomainValue) mRightSubEvaluator.evaluate(currentState);

		if (firstResult.getValue().equals(SignValues.BOTTOM) || secondResult.getValue().equals(SignValues.BOTTOM)) {
			return currentState.bottomState();
		}

		SignDomainState newState = currentState.createCopy();

		final boolean compResult = evaluateComparisonOperators(firstResult, secondResult);

		switch (mOperator) {
		case LOGICIFF:
		case LOGICIMPLIES:
		case LOGICAND:
		case LOGICOR:
		case COMPLT:
		case COMPGT:
		case COMPLEQ:
		case COMPGEQ:
			throw new UnsupportedOperationException("The operator " + mOperator.toString() + " is not implemented.");
		case COMPNEQ:
			if (firstResult.getValue().equals(SignValues.TOP) || secondResult.getValue().equals(SignValues.TOP)) {
				return newState;
			}

			// TODO How to deal with inequalities in the sign domain?
			if (!compResult) {
				return newState.bottomState();
			}

			return newState;
		case COMPEQ:
			if (firstResult.getValue().equals(SignValues.TOP) || secondResult.getValue().equals(SignValues.TOP)) {
				return newState;
			}

			if (compResult) {
				// Compute new state, only of the form x == 3 or 3 == x for now.
				if (mLeftSubEvaluator instanceof SignLogicalSingletonVariableExpressionEvaluator
						&& !(mRightSubEvaluator instanceof SignLogicalSingletonVariableExpressionEvaluator)) {
					final SignLogicalSingletonVariableExpressionEvaluator leftie =
							(SignLogicalSingletonVariableExpressionEvaluator) mLeftSubEvaluator;
					final SignDomainState intersecterino = currentState.createCopy();
					// SignDomainState<CodeBlock, IBoogieVar> rightState = (SignDomainState<CodeBlock, IBoogieVar>)
					// secondLogicalInterpretation;
					// intersecterino.setValue(leftie.mVariableName, rightState.getValues().get(leftie.mVariableName));

					newState = newState.intersect(intersecterino);
				} else if (!(mLeftSubEvaluator instanceof SignLogicalSingletonVariableExpressionEvaluator)
						&& mRightSubEvaluator instanceof SignLogicalSingletonVariableExpressionEvaluator) {
					final SignLogicalSingletonVariableExpressionEvaluator rightie =
							(SignLogicalSingletonVariableExpressionEvaluator) mRightSubEvaluator;
					final SignDomainState intersecterino = currentState.createCopy();
					// SignDomainState<CodeBlock, IBoogieVar> leftState = (SignDomainState<CodeBlock, IBoogieVar>)
					// firstLogicalInterpretation;
					// intersecterino.setValue(rightie.mVariableName, leftState.getValues().get(rightie.mVariableName));

					return newState.intersect(intersecterino);
				}
			}
		case COMPPO:
			// return evaluateLogicalOperator(currentState, firstResult, secondResult);
		case BITVECCONCAT:
		case ARITHMUL:
		case ARITHDIV:
		case ARITHMOD:
		case ARITHPLUS:
		case ARITHMINUS:
			throw new UnsupportedOperationException("The operator " + mOperator.toString() + " is not implemented.");
		default:
			mLogger.warn("Loss of precision while interpreting the logical expression " + toString());
			return currentState.createCopy();
		// throw new UnsupportedOperationException("The operator " + mOperator.toString() + " is not implemented.");
		}
	}

	private boolean evaluateComparisonOperators(SignDomainValue firstResult, SignDomainValue secondResult) {

		switch (mOperator) {
		case COMPLT:
			return evaluateLTComparison(firstResult, secondResult);
		case COMPGT:
			return evaluateGTComparison(firstResult, secondResult);
		case COMPLEQ:
		case COMPGEQ:
		case COMPNEQ:
			return evaluateNEComparison(firstResult, secondResult);
		case COMPEQ:
			return evaluateEQComparison(firstResult, secondResult);
		default:
			throw new UnsupportedOperationException("The operator " + mOperator.toString() + " is not implemented.");
		}
	}

	private boolean evaluateEQComparison(SignDomainValue firstResult, SignDomainValue secondResult) {
		if (firstResult.equals(secondResult)) {
			return true;
		} else {
			return false;
		}
	}

	private boolean evaluateNEComparison(SignDomainValue firstResult, SignDomainValue secondResult) {
		if (firstResult.getValue() == SignValues.ZERO && secondResult.getValue() == SignValues.ZERO) {
			return false;
		}

		return true;
	}

	private boolean evaluateGTComparison(SignDomainValue firstResult, SignDomainValue secondResult) {
		if (firstResult.getValue() == secondResult.getValue() || firstResult.getValue() == SignValues.BOTTOM
				|| secondResult.getValue() == SignValues.BOTTOM || firstResult.getValue() == SignValues.TOP
				|| secondResult.getValue() == SignValues.TOP) {
			return false;
		}

		if (firstResult.getValue() == SignValues.POSITIVE && !(secondResult.getValue() == SignValues.POSITIVE)) {
			return true;
		}

		if (firstResult.getValue() == SignValues.ZERO && secondResult.getValue() == SignValues.NEGATIVE) {
			return true;
		}

		return false;
	}

	private boolean evaluateLTComparison(SignDomainValue firstResult, SignDomainValue secondResult) {
		if (firstResult.equals(secondResult)) {
			return false;
		}

		if (firstResult.getValue() == SignValues.NEGATIVE && !(secondResult.getValue() == SignValues.NEGATIVE)) {
			return true;
		}

		if (firstResult.getValue() == SignValues.ZERO && secondResult.getValue() == SignValues.POSITIVE) {
			return true;
		}
		return false;
	}

	// protected BooleanValue logicalEvaluation(SignDomainState currentState) {
	//
	// switch (mOperator) {
	// case COMPEQ:
	// return mLeftSubEvaluator.booleanValue().intersect(mRightSubEvaluator.booleanValue());
	// case COMPNEQ:
	// return mLeftSubEvaluator.booleanValue().intersect(mRightSubEvaluator.booleanValue().neg());
	// case LOGICIMPLIES:
	// return mLeftSubEvaluator.booleanValue().or(mRightSubEvaluator.booleanValue());
	// case LOGICIFF:
	// return (mLeftSubEvaluator.booleanValue().and(mRightSubEvaluator.booleanValue())
	// .or((mLeftSubEvaluator.booleanValue().neg().and(mRightSubEvaluator.booleanValue().neg()))));
	// case LOGICOR:
	// return mLeftSubEvaluator.booleanValue().or(mRightSubEvaluator.booleanValue());
	// default:
	// throw new UnsupportedOperationException("Operator " + mOperator + " not yet implemented.");
	// // TODO: implement other cases
	// }
	// }

	@Override
	public boolean containsBool() {
		// TODO Auto-generated method stub
		return false;
	}
}
