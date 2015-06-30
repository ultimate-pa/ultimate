package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import java.math.BigDecimal;
import java.util.HashSet;
import java.util.Set;

/**
 * Represents a single decimal expression in the {@link SignDomain}.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SignSingletonDecimalExpressionEvaluator extends SignSingletonValueExpressionEvaluator<BigDecimal> {

	public SignSingletonDecimalExpressionEvaluator(String value) {
		super(value);
	}

	@Override
	protected BigDecimal instantiate(String value) {
		BigDecimal number;
		try {
			number = new BigDecimal(value);
		} catch (NumberFormatException e) {
			throw new UnsupportedOperationException("The value \"" + value
			        + "\" cannot be transformed to a decimal number.");
		}

		return number;
	}

	@Override
	protected int getSignum() {
		return mValue.signum();
	}

	@Override
	public Set<String> getVarIdentifiers() {
		return new HashSet<String>();
	}

}
