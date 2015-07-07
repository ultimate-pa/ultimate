package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.ILogicalEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Represents a boolean expression in the {@link SignDomain}. This requires the program to be analyzed to contain the
 * literals "True" or "False". If "True" is read, the value of {@link this} is <code>true</code>, otherwise
 * <code>false</code>.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SignLogicalSingletonValueExpressionEvaluator extends SignSingletonValueExpressionEvaluator<Boolean>
        implements ILogicalEvaluator<Values, CodeBlock, BoogieVar> {

	public SignLogicalSingletonValueExpressionEvaluator(String value) {
		super(value);
	}

	@Override
	public void setOperator(Object operator) {
		throw new UnsupportedOperationException("Setting the operator for this kind of expression is not permitted.");
	}

	@Override
	public IEvaluationResult<Values> evaluate(IAbstractState<CodeBlock, BoogieVar> currentState) {
		if (mValue) {
			return new SignDomainValue(Values.POSITIVE);
		} else {
			return new SignDomainValue(Values.NEGATIVE);
		}
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> logicallyInterpret(IAbstractState<CodeBlock, BoogieVar> currentState) {
		return currentState;
	}

	@Override
	protected Boolean instantiate(String value) {
		Boolean bool = new Boolean(value);

		return bool;
	}

	@Override
	protected int getSignum() {
		return 0;
	}

}
