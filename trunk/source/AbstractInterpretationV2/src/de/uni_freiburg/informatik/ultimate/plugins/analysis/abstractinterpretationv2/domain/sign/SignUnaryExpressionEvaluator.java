package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class SignUnaryExpressionEvaluator implements IEvaluator<SignDomainValue.Values, CodeBlock, BoogieVar> {

	private IEvaluator<SignDomainValue.Values, CodeBlock, BoogieVar> mSubEvaluator;
	private UnaryExpression.Operator mOperator;

	@Override
	public void addSubEvaluator(IEvaluator<SignDomainValue.Values, CodeBlock, BoogieVar> evaluator) {

		assert mSubEvaluator == null;
		assert evaluator != null;

		mSubEvaluator = evaluator;
	}

	protected void setOperator(UnaryExpression.Operator operator) {
		mOperator = operator;
	}

	@Override
	public IEvaluationResult<SignDomainValue.Values> evaluate(IAbstractState<CodeBlock, BoogieVar> oldState) {
		final IEvaluationResult<SignDomainValue.Values> subEvalResult = mSubEvaluator.evaluate(oldState);

		IEvaluationResult<SignDomainValue.Values> endResult;

		switch (mOperator) {
		case ARITHNEGATIVE:
			endResult = negateValue(subEvalResult.getResult());
			break;
		default:
			throw new UnsupportedOperationException("The operator " + mOperator.toString() + " is not implemented.");
		}

		return endResult;
	}

	private IEvaluationResult<SignDomainValue.Values> negateValue(SignDomainValue.Values value) {
		assert value != null;

		switch (value) {
		case POSITIVE:
			return new SignDomainValue(Values.NEGATIVE);
		case NEGATIVE:
			return new SignDomainValue(Values.POSITIVE);
		case TOP:
			return new SignDomainValue(Values.TOP);
		case BOTTOM:
			return new SignDomainValue(Values.BOTTOM);
		case ZERO:
			return new SignDomainValue(Values.ZERO);
		default:
			throw new UnsupportedOperationException("The sign domain value " + value.toString()
			        + " is not implemented.");
		}
	}

	@Override
	public boolean hasFreeOperands() {
		return (mSubEvaluator == null);
	}

}
