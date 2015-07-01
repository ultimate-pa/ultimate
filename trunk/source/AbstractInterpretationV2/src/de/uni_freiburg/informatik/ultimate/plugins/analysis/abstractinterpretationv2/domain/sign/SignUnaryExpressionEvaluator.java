package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class SignUnaryExpressionEvaluator implements IEvaluator<Values, CodeBlock, BoogieVar> {

	private IEvaluator<?, ?, ?> mSubEvaluator;
	private UnaryExpression.Operator mOperator;

	@Override
	public void addSubEvaluator(IEvaluator<?, ?, ?> evaluator) {

		assert mSubEvaluator == null;
		assert evaluator != null;

		mSubEvaluator = evaluator;
	}

	protected void setOperator(UnaryExpression.Operator operator) {
		mOperator = operator;
	}

	@Override
	public IEvaluationResult<?> evaluate(IAbstractState<?, ?> oldState) {
		if (!mSubEvaluator.getType().equals(Values.class)) {
			throw new UnsupportedOperationException("Unsupported Type of the sub evaluator.");
		}

		IEvaluator<Values, CodeBlock, BoogieVar> castedSubEvaluator = (IEvaluator<Values, CodeBlock, BoogieVar>) mSubEvaluator;
		final IEvaluationResult<Values> subEvalResult = (IEvaluationResult<Values>) castedSubEvaluator
		        .evaluate(oldState);

		IEvaluationResult<Values> endResult;

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

	@Override
	public Set<String> getVarIdentifiers() {
		return mSubEvaluator.getVarIdentifiers();
	}

	@Override
	public Class<Values> getType() {
		return Values.class;
	}
}
