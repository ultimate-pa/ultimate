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
 * Represents an expression that consists of a single variable in the {@link SignDomain}.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SignSingletonVariableExpressionEvaluator implements IEvaluator<Values, CodeBlock, BoogieVar> {

	protected String mVariableName;
	protected final SignStateConverter<CodeBlock, BoogieVar> mStateConverter;
	private final Set<String> mVariableSet;

	/**
	 * Constructor that creates a singleton variable expression evaluator in the sign domain.
	 * 
	 * @param variableName
	 *            The name of the variable.
	 * @param stateConverter
	 *            The interval domain state converter.
	 */
	public SignSingletonVariableExpressionEvaluator(String variableName,
	        SignStateConverter<CodeBlock, BoogieVar> stateConverter) {
		mVariableName = variableName;
		mStateConverter = stateConverter;
		mVariableSet = new HashSet<String>();
	}

	@Override
	public final void addSubEvaluator(IEvaluator<Values, CodeBlock, BoogieVar> evaluator) {
		throw new UnsupportedOperationException("A sub evaluator cannot be added to a singleton expression type.");
	}

	@Override
	public final boolean hasFreeOperands() {
		return false;
	}

	@Override
	public final IEvaluationResult<Values> evaluate(IAbstractState<CodeBlock, BoogieVar> currentState) {
		final SignDomainState<CodeBlock, BoogieVar> concreteState = mStateConverter.getCheckedState(currentState);

		final SignDomainValue val = concreteState.getValues().get(mVariableName);

		if (val == null) {
			throw new UnsupportedOperationException("The variable with name " + mVariableName
			        + " has not been found in the current abstract state.");
		}

		return new SignDomainValue(val.getResult());
	}

	@Override
	public Set<String> getVarIdentifiers() {
		return mVariableSet;
	}
}
