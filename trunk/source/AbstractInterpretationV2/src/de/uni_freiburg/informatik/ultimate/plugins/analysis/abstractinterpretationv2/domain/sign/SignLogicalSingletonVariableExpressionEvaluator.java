package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.ILogicalEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class SignLogicalSingletonVariableExpressionEvaluator extends SignSingletonVariableExpressionEvaluator implements
        ILogicalEvaluator<Values, CodeBlock, BoogieVar> {

	public SignLogicalSingletonVariableExpressionEvaluator(String variableName,
	        SignStateConverter<CodeBlock, BoogieVar> stateConverter) {
		super(variableName, stateConverter);
	}

	@Override
	public void setOperator(Object operator) {
		throw new UnsupportedOperationException("Operation not permitted.");
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> logicallyInterpret(IAbstractState<CodeBlock, BoogieVar> currentState) {
		assert currentState.containsVariable(mVariableName);

		final SignDomainState<CodeBlock, BoogieVar> convertedState = mStateConverter.getCheckedState(currentState);

		final BoogieVar var = convertedState.getVariables().get(mVariableName);

		final BoogieType varType = (BoogieType) var.getIType();

		// TODO: Check type for bool. How to do that?

		final SignDomainValue value = convertedState.getValues().get(mVariableName);

		IAbstractState<CodeBlock, BoogieVar> newState = currentState.copy();

		return newState;
	}

	protected final SignDomainValue getBooleanValue(IAbstractState<CodeBlock, BoogieVar> currentState) {

		assert currentState.containsVariable(mVariableName);

		final SignDomainState<CodeBlock, BoogieVar> convertedState = mStateConverter.getCheckedState(currentState);

		final SignDomainValue value = convertedState.getValues().get(mVariableName);

		SignDomainValue newValue;

		switch (value.getResult()) {
		case NEGATIVE:
			return new SignDomainValue(Values.NEGATIVE);
		case POSITIVE:
			return new SignDomainValue(Values.POSITIVE);
		case BOTTOM:
			return new SignDomainValue(Values.BOTTOM);
		default:
			throw new UnsupportedOperationException("The value " + value.getResult().toString()
			        + " is no valid boolean sign domain value.");
		}
	}

	@Override
    public boolean logicalEvaluation(IAbstractState<CodeBlock, BoogieVar> currentState) {
		
		assert currentState.containsVariable(mVariableName);
		
		final SignDomainState<CodeBlock, BoogieVar> convertedState = mStateConverter.getCheckedState(currentState);

		final SignDomainValue value = convertedState.getValues().get(mVariableName);

		SignDomainValue newValue;

		switch (value.getResult()) {
		case NEGATIVE:
			return false;
		case POSITIVE:
			return true;
		case BOTTOM:
			return false;
		default:
			throw new UnsupportedOperationException("The value " + value.getResult().toString()
			        + " is no valid boolean sign domain value.");
		}
    }

}
