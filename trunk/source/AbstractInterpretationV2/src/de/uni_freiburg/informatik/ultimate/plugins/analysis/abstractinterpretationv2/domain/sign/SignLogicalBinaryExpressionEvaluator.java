package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.ILogicalEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class SignLogicalBinaryExpressionEvaluator extends SignBinaryExpressionEvaluator implements
        ILogicalEvaluator<Values, CodeBlock, BoogieVar> {

	public SignLogicalBinaryExpressionEvaluator() {
		super();
	}

	@Override
	public IEvaluationResult<Values> evaluate(IAbstractState<CodeBlock, BoogieVar> currentState) {
		for (String var : mLeftSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}
		for (String var : mRightSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}

		final IEvaluationResult<Values> firstResult = mLeftSubEvaluator.evaluate(currentState);
		final IEvaluationResult<Values> secondResult = mRightSubEvaluator.evaluate(currentState);

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
			return evaluateComparisonOperators(firstResult.getResult(), secondResult.getResult());
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
			throw new UnsupportedOperationException("The operator " + mOperator.toString() + " is not implemented.");
		}
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> logicallyInterpret(IAbstractState<CodeBlock, BoogieVar> currentState) {

		final IEvaluationResult<Values> firstResult = mLeftSubEvaluator.evaluate(currentState);
		final IEvaluationResult<Values> secondResult = mRightSubEvaluator.evaluate(currentState);
		final IAbstractState<CodeBlock, BoogieVar> firstLogicalInterpretation = ((ILogicalEvaluator<Values, CodeBlock, BoogieVar>) mLeftSubEvaluator)
		        .logicallyInterpret(currentState);
		final IAbstractState<CodeBlock, BoogieVar> secondLogicalInterpretation = ((ILogicalEvaluator<Values, CodeBlock, BoogieVar>) mRightSubEvaluator)
		        .logicallyInterpret(currentState);

		SignDomainState<CodeBlock, BoogieVar> newState = (SignDomainState<CodeBlock, BoogieVar>) currentState.copy();

		switch (mOperator) {
		// case LOGICIFF:
		// case LOGICIMPLIES:
		case LOGICAND:
		case LOGICOR:
		case COMPLT:
		case COMPGT:
		case COMPLEQ:
		case COMPGEQ:
		case COMPNEQ:
			IEvaluationResult<Values> compResult = evaluateComparisonOperators(firstResult.getResult(),
			        secondResult.getResult());

			if (compResult.getResult().equals(Values.POSITIVE)) {
				// Compute new state
				if (mLeftSubEvaluator instanceof SignLogicalSingletonVariableExpressionEvaluator) {
					SignLogicalSingletonVariableExpressionEvaluator leftie = (SignLogicalSingletonVariableExpressionEvaluator) mLeftSubEvaluator;
					SignDomainState<CodeBlock, BoogieVar> intersecterino = (SignDomainState<CodeBlock, BoogieVar>) currentState
					        .copy();
					intersecterino.setValue(leftie.mVariableName, (SignDomainValue) secondResult);
					
					newState = newState.intersect(intersecterino);
				}

			} else {
				newState.setToBottom();
			}

			return newState;
		case COMPEQ:
		case COMPPO:
			// return evaluateLogicalOperator(currentState, firstResult, secondResult);
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
			throw new UnsupportedOperationException("The operator " + mOperator.toString() + " is not implemented.");
		}
	}

	private IEvaluationResult<?> evaluateLogicalOperator(IAbstractState<CodeBlock, BoogieVar> currentState,
	        IEvaluationResult<?> firstResult, IEvaluationResult<?> secondResult) {

		if (firstResult instanceof SignDomainValue && secondResult instanceof SignDomainValue) {
			final IEvaluationResult<Values> castedFirst = (IEvaluationResult<Values>) firstResult;
			final IEvaluationResult<Values> castedSecond = (IEvaluationResult<Values>) secondResult;

			return evaluateComparisonOperators(castedFirst.getResult(), castedSecond.getResult());
		}

		if (firstResult instanceof SignLogicalSingletonVariableExpressionEvaluator
		        && secondResult instanceof SignDomainValue) {

			final SignLogicalSingletonVariableExpressionEvaluator firstVariable = (SignLogicalSingletonVariableExpressionEvaluator) firstResult;

			final IEvaluationResult<Values> first = firstVariable.getBooleanValue(currentState);
			final IEvaluationResult<Values> second = (IEvaluationResult<Values>) secondResult;

			return evaluateComparisonOperators(first.getResult(), second.getResult());
		}

		throw new UnsupportedOperationException("Not implemented.");
	}

	private IEvaluationResult<Values> evaluateComparisonOperators(Values firstResult, Values secondResult) {

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
			if (firstResult.equals(secondResult)) {
				return new SignDomainValue(Values.POSITIVE);
			} else {
				return new SignDomainValue(Values.NEGATIVE);
			}
		default:
			throw new UnsupportedOperationException("The operator " + mOperator.toString() + " is not implemented.");
		}
	}

	private IEvaluationResult<Values> evaluateNEComparison(Values firstResult, Values secondResult) {
		if (firstResult.equals(Values.BOTTOM) || secondResult.equals(Values.BOTTOM)) {
			return new SignDomainValue(Values.BOTTOM);
		}

		if (firstResult.equals(Values.ZERO) && secondResult.equals(Values.ZERO)) {
			return new SignDomainValue(Values.NEGATIVE);
		}

		return new SignDomainValue(Values.POSITIVE);
	}

	private IEvaluationResult<Values> evaluateGTComparison(Values firstResult, Values secondResult) {
		if (firstResult.equals(secondResult) || firstResult.equals(Values.BOTTOM) || secondResult.equals(Values.BOTTOM)
		        || firstResult.equals(Values.TOP) || secondResult.equals(Values.TOP)) {
			return new SignDomainValue(Values.NEGATIVE);
		}

		if (firstResult.equals(Values.POSITIVE) && !secondResult.equals(Values.POSITIVE)) {
			return new SignDomainValue(Values.POSITIVE);
		}

		if (firstResult.equals(Values.ZERO) && secondResult.equals(Values.NEGATIVE)) {
			return new SignDomainValue(Values.POSITIVE);
		}

		return new SignDomainValue(Values.NEGATIVE);
	}

	private IEvaluationResult<Values> evaluateLTComparison(Values firstResult, Values secondResult) {
		if (firstResult.equals(Values.BOTTOM) || secondResult.equals(Values.BOTTOM)) {
			return new SignDomainValue(Values.BOTTOM);
		}

		if (firstResult.equals(Values.TOP) || secondResult.equals(Values.TOP)) {
			return new SignDomainValue(Values.TOP);
		}

		if (firstResult.equals(secondResult)) {
			return new SignDomainValue(Values.NEGATIVE);
		}

		if (firstResult.equals(Values.NEGATIVE) && !secondResult.equals(Values.NEGATIVE)) {
			return new SignDomainValue(Values.POSITIVE);
		}

		if (firstResult.equals(Values.ZERO) && secondResult.equals(Values.POSITIVE)) {
			return new SignDomainValue(Values.POSITIVE);
		}
		return new SignDomainValue(Values.NEGATIVE);
	}
}
