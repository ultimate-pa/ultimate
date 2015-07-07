package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.ILogicalEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Representation of a logical singleton expression evaluator for decimal values of the {@link SignDomain}.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SignLogicalSingletonDecimalExpressionEvaluator extends SignSingletonDecimalExpressionEvaluator implements
        ILogicalEvaluator<Values, CodeBlock, BoogieVar> {

	public SignLogicalSingletonDecimalExpressionEvaluator(String value) {
		super(value);
	}

	@Override
	public void setOperator(Object operator) {
		throw new UnsupportedOperationException(
		        "Setting an operator fo a singleton decimal expression evaluator is not permitted.");
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> logicallyInterpret(IAbstractState<CodeBlock, BoogieVar> currentState) {
		return currentState.copy();
	}

}
