package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import java.math.BigInteger;

/**
 * Represents a single integer expression in the {@link SignDomain}.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SignSingletonIntegerExpressionEvaluator extends SignSingletonValueExpressionEvaluator<BigInteger> {

	protected SignSingletonIntegerExpressionEvaluator(String value) {
		super(value);
	}

	@Override
	protected final BigInteger instantiate(String value) {
		BigInteger number;
		try {
			number = new BigInteger(value);
		} catch (NumberFormatException e) {
			throw new UnsupportedOperationException("The value \"" + value + "\" cannot be transformed to an integer.");
		}
		return number;
	}

	@Override
	protected final int getSignum() {
		return mValue.signum();
	}
}
