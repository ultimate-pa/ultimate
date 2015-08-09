package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.ILogicalEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Represents a logical unary expression evaluator in the {@link SignDomain} that exposes the method
 * {@link #logicallyInterpret(IAbstractState)} to return an abstract state when dealing with {@link ILogicalEvaluator}s.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SignLogicalUnaryExpressionEvaluator extends SignUnaryExpressionEvaluator implements
        ILogicalEvaluator<Values, CodeBlock, BoogieVar> {

	@Override
	public IAbstractState<CodeBlock, BoogieVar> logicallyInterpret(IAbstractState<CodeBlock, BoogieVar> currentState) {
		final ILogicalEvaluator<Values, CodeBlock, BoogieVar> castedEvaluator = (ILogicalEvaluator<Values, CodeBlock, BoogieVar>) mSubEvaluator;
		return castedEvaluator.logicallyInterpret(currentState);
	}

	@Override
    public boolean logicalEvaluation(IAbstractState<CodeBlock, BoogieVar> currentState) {
		final ILogicalEvaluator<Values, CodeBlock, BoogieVar> castedEvaluator = (ILogicalEvaluator<Values, CodeBlock, BoogieVar>) mSubEvaluator;
		
		switch (mOperator) {
		case LOGICNEG:
			return !castedEvaluator.logicalEvaluation(currentState);
		default:
			return castedEvaluator.logicalEvaluation(currentState);
		}
    }

}
