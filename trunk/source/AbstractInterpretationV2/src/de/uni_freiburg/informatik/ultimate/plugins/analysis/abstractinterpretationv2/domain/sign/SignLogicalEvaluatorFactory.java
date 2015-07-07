package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SignLogicalEvaluatorFactory implements IEvaluatorFactory<Values, CodeBlock, BoogieVar> {

	SignStateConverter<CodeBlock, BoogieVar> mStateConverter;

	public SignLogicalEvaluatorFactory(SignStateConverter<CodeBlock, BoogieVar> stateConverter) {
		mStateConverter = stateConverter;
	}

	@Override
	public INAryEvaluator<Values, CodeBlock, BoogieVar> createNAryExpressionEvaluator(int arity) {

		assert arity >= 1 && arity <= 2;

		switch (arity) {
		case 1:
			return new SignLogicalUnaryExpressionEvaluator();
		case 2:
			return new SignLogicalBinaryExpressionEvaluator();
		default:
			throw new UnsupportedOperationException("Arity of " + arity + " is not implemented.");
		}
	}

	@Override
	public IEvaluator<Values, CodeBlock, BoogieVar> createSingletonValueExpressionEvaluator(String value,
	        Class<?> valueType) {

		if (valueType.equals(BigInteger.class)) {
			return new SignLogicalSingletonIntegerExpressionEvaluator(value);
		}

		if (valueType.equals(BigDecimal.class)) {
			return new SignLogicalSingletonDecimalExpressionEvaluator(value);
		}

		if (valueType.equals(Boolean.class)) {
			return new SignLogicalSingletonValueExpressionEvaluator(value);
		}

		throw new UnsupportedOperationException("The type " + valueType.toString() + " is not supported.");
	}

	@Override
	public IEvaluator<Values, CodeBlock, BoogieVar> createSingletonVariableExpressionEvaluator(String variableName) {
		return new SignLogicalSingletonVariableExpressionEvaluator(variableName, mStateConverter);
	}

}
