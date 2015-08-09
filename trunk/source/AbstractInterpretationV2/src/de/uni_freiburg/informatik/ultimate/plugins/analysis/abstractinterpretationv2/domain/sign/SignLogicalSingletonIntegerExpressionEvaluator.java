package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.ILogicalEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Representation of a logical singleton expression evaluator for integer values of the {@link SignDomain}.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SignLogicalSingletonIntegerExpressionEvaluator extends SignSingletonIntegerExpressionEvaluator implements
        ILogicalEvaluator<Values, CodeBlock, BoogieVar> {

	protected SignLogicalSingletonIntegerExpressionEvaluator(String value) {
		super(value);
	}

	@Override
	public void setOperator(Object operator) {
		throw new UnsupportedOperationException(
		        "Setting the operator on an integer expression evaluator is not permitted.");
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> logicallyInterpret(IAbstractState<CodeBlock, BoogieVar> currentState) {
		return currentState.copy();
	}

	@Override
    public boolean logicalEvaluation(IAbstractState<CodeBlock, BoogieVar> currentState) {
		// TODO Think about this if this is right.
		return false;
    }

}
