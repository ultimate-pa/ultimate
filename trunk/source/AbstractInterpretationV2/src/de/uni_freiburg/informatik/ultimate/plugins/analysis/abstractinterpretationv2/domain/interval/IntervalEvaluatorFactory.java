package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Factory for evaluators of the interval domain.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class IntervalEvaluatorFactory implements IEvaluatorFactory<IntervalDomainValue, CodeBlock, BoogieVar> {

	private static final int ARITY_MIN = 1;
	private static final int ARITY_MAX = 2;
	private static final int BUFFER_MAX = 100;

	private final IntervalStateConverter<CodeBlock, BoogieVar> mStateConverter;
	private final IUltimateServiceProvider mServices;

	/**
	 * Creates a new evaluator factory for the interval domain.
	 * 
	 * @param services
	 *            The Ultimate services.
	 * @param stateConverter
	 *            The state converter in the interval domain.
	 */
	public IntervalEvaluatorFactory(IUltimateServiceProvider services,
	        IntervalStateConverter<CodeBlock, BoogieVar> stateConverter) {
		mServices = services;
		mStateConverter = stateConverter;
	}

	@Override
	public INAryEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> createNAryExpressionEvaluator(int arity) {

		assert arity >= ARITY_MIN && arity <= ARITY_MAX;

		switch (arity) {
		case ARITY_MIN:
		case ARITY_MAX:
		default:
			final StringBuilder stringBuilder = new StringBuilder(BUFFER_MAX);
			stringBuilder.append("Arity of ").append(arity).append(" is not implemented.");
			throw new UnsupportedOperationException(stringBuilder.toString());
		}
	}

	@Override
	public IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> createSingletonValueExpressionEvaluator(String value,
	        Class<?> valueType) {

		if (valueType.equals(BigInteger.class)) {
			return new IntervalUnaryExpressionEvaluator();
		}

		if (valueType.equals(BigDecimal.class)) {
			return new IntervalBinaryExpressionEvaluator(mServices);
		}

		throw new UnsupportedOperationException("The type " + valueType.toString() + " is not implemented.");
	}

	@Override
	public IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> createSingletonVariableExpressionEvaluator(
	        String variableName) {
		return new IntervalSingletonVariableExpressionEvaluator(variableName, mStateConverter);
	}
}
