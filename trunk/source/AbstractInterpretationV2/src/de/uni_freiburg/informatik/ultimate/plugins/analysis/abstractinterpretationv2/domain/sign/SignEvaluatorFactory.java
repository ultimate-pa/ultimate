package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class SignEvaluatorFactory implements IEvaluatorFactory<Values, CodeBlock, BoogieVar> {

	@Override
	public IEvaluator<Values, CodeBlock, BoogieVar> createNAryExpressionEvaluator(int arity) {
		assert arity >= 0 && arity <= 2;

		switch (arity) {
		case 1:
			return new SignUnaryExpressionEvaluator();
		case 2:
			return new SignBinaryExpressionEvaluator();
		default:
			throw new UnsupportedOperationException("Arity of " + arity + " is not implemented.");
		}
	}

	@Override
    public IEvaluator<Values, CodeBlock, BoogieVar> createSingletonValueExpressionEvaluator() {
		// TODO Auto-generated method stub
		return null;
    }

	@Override
    public IEvaluator<Values, CodeBlock, BoogieVar> createSingletonVariableExpressionEvaluator() {
	    // TODO Auto-generated method stub
	    return null;
    }

}
