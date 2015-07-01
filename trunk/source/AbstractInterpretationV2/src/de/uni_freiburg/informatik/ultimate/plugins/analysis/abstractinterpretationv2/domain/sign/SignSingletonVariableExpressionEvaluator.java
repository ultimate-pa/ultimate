package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Represents an expression that consists of a single variable in the
 * {@link SignDomain}.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public final class SignSingletonVariableExpressionEvaluator implements IEvaluator<Values, CodeBlock, BoogieVar> {

	private String mVariableName;
	private SignStateConverter<CodeBlock, BoogieVar> mStateConverter;
	private Set<String> mVariableSet;

	public SignSingletonVariableExpressionEvaluator(String variableName,
	        SignStateConverter<CodeBlock, BoogieVar> stateConverter) {
		mVariableName = variableName;
		mStateConverter = stateConverter;
		mVariableSet = new HashSet<String>();
	}

	@Override
	public final void addSubEvaluator(IEvaluator<?, ?, ?> evaluator) {
		throw new UnsupportedOperationException("A sub evaluator cannot be added to a singleton expression type.");
	}

	@Override
	public final boolean hasFreeOperands() {
		return false;
	}

	@Override
	public final IEvaluationResult<Values> evaluate(IAbstractState<?, ?> currentState) {
		SignDomainState<CodeBlock, BoogieVar> concreteState = mStateConverter
		        .getCheckedState((IAbstractState<CodeBlock, BoogieVar>) currentState);

		SignDomainValue val = concreteState.getValues().get(mVariableName);

		if (val == null) {
			throw new UnsupportedOperationException("The variable with name " + mVariableName
			        + " has not been found in the current abstract state.");
		}

		return val;
	}

	@Override
	public Set<String> getVarIdentifiers() {
		return mVariableSet;
	}

	@Override
    public Class<Values> getType() {
	    return Values.class;
    }
}
