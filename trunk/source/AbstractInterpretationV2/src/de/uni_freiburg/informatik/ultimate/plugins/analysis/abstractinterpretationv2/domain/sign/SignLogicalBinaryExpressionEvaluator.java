package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.ILogicalEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class SignLogicalBinaryExpressionEvaluator extends SignBinaryExpressionEvaluator implements
        ILogicalEvaluator<Values, CodeBlock, BoogieVar> {

	private ILogicalEvaluator<?, CodeBlock, BoogieVar> mLeftSubEvaluator;
	private ILogicalEvaluator<?, CodeBlock, BoogieVar> mRightSubEvaluator;
	private BinaryExpression.Operator mOperator;

	public SignLogicalBinaryExpressionEvaluator() {
		super();
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> logicallyInterpret(IAbstractState<CodeBlock, BoogieVar> currentState) {

		final IEvaluationResult<?> firstResult = mLeftSubEvaluator.evaluate(currentState);
		final IEvaluationResult<?> secondResult = mRightSubEvaluator.evaluate(currentState);
		final IAbstractState<CodeBlock, BoogieVar> firstLogicalInterpretation = mLeftSubEvaluator
		        .logicallyInterpret(currentState);
		final IAbstractState<CodeBlock, BoogieVar> secondLogicalInterpretation = mRightSubEvaluator
		        .logicallyInterpret(currentState);

		switch (mOperator) {
		case LOGICIFF:
		case LOGICIMPLIES:
		case LOGICAND:
		case LOGICOR:
		case COMPLT:
		case COMPGT:
		case COMPLEQ:
		case COMPGEQ:
		case COMPNEQ:
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
			IEvaluationResult<Values> castedFirst = (IEvaluationResult<Values>) firstResult;
			IEvaluationResult<Values> castedSecond = (IEvaluationResult<Values>) secondResult;

			return evaluateComparisonOperators(castedFirst.getResult(), castedSecond.getResult());
		} else {
			throw new UnsupportedOperationException("Not implemented.");
		}
	}

	private IEvaluationResult<?> evaluateComparisonOperators(Values firstResult, Values secondResult) {

		switch (mOperator) {
		case COMPLT:
			return evaluateLTComparison(firstResult, secondResult);
		case COMPGT:
			return evaluateGTComparison(firstResult, secondResult);
		case COMPLEQ:
		case COMPGEQ:
		case COMPNEQ:
			if ((firstResult.equals(Values.BOTTOM) && !secondResult.equals(Values.BOTTOM))
			        || (!firstResult.equals(Values.BOTTOM) && secondResult.equals(Values.BOTTOM))) {
				return new SignDomainValue(Values.NEGATIVE);
			}

			if (firstResult.equals(Values.ZERO) && secondResult.equals(Values.ZERO)) {
				return new SignDomainValue(Values.NEGATIVE);
			}

			return new SignDomainValue(Values.TOP);
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

	private IEvaluationResult<?> evaluateGTComparison(Values firstResult, Values secondResult) {
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

	private IEvaluationResult<?> evaluateLTComparison(Values firstResult, Values secondResult) {
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
