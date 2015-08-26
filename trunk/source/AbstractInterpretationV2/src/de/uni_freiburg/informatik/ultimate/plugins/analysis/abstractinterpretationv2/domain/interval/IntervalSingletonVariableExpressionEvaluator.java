package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Represents an expression that consists of a single variable in the {@link IntervalDomain}.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class IntervalSingletonVariableExpressionEvaluator implements
        IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> {

	protected String mVariableName;
	protected final IntervalStateConverter<CodeBlock, BoogieVar> mStateConverter;
	private final Set<String> mVariableSet;

	/**
	 * Constructor that creates a singleton variable expression evaluator in the interval domain.
	 * 
	 * @param variableName
	 *            The name of the variable.
	 * @param stateConverter
	 *            The interval domain state converter.
	 */
	public IntervalSingletonVariableExpressionEvaluator(String variableName,
	        IntervalStateConverter<CodeBlock, BoogieVar> stateConverter) {
		mVariableName = variableName;
		mStateConverter = stateConverter;
		mVariableSet = new HashSet<String>();
	}

	@Override
	public IEvaluationResult<IntervalDomainValue> evaluate(IAbstractState<CodeBlock, BoogieVar> currentState) {

		final IntervalDomainState<CodeBlock, BoogieVar> concreteState = mStateConverter.getCheckedState(currentState);

		final IntervalDomainValue val = concreteState.getValues().get(mVariableName);

		if (val == null) {
			throw new UnsupportedOperationException("The variable with name " + mVariableName
			        + " has not been found in the current abstract state.");
		}

		return new IntervalDomainValue(val.getLower(), val.getUpper());
	}

	@Override
	public void addSubEvaluator(IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> evaluator) {
		throw new UnsupportedOperationException(
		        "A sub evaluator cannot be added to a singleton variable expression evaluator.");
	}

	@Override
	public Set<String> getVarIdentifiers() {
		return mVariableSet;
	}

	@Override
	public boolean hasFreeOperands() {
		return false;
	}

}
