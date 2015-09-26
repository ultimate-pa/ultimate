/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.intervaldomain;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IValueMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IValueWideningOperator;

/**
 * @author Christopher Dillo
 *
 */
public class IntervalValueFactory implements IAbstractValueFactory<Interval> {

	private static final String s_domainID = "INTERVAL";

	private final Logger m_logger;

	public IntervalValueFactory(Logger logger) {
		m_logger = logger;
	}

	public static String getDomainID() {
		return s_domainID;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeValue(java.lang.Object)
	 */
	@Override
	public IntervalValue makeValue(Interval value) {
		return new IntervalValue(value, this, m_logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeTopValue()
	 */
	@Override
	public IntervalValue makeTopValue() {
		return new IntervalValue(new Interval(Rational.NEGATIVE_INFINITY,
				Rational.POSITIVE_INFINITY), this, m_logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeBottomValue()
	 */
	@Override
	public IntervalValue makeBottomValue() {
		return new IntervalValue(new Interval(), this, m_logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeIntegerValue(java.lang.String)
	 */
	@Override
	public IntervalValue makeIntegerValue(String integer) {
		BigInteger bigInt;
		try {
			bigInt = new BigInteger(integer);
		} catch (NumberFormatException e) {
			m_logger.warn(String
					.format("Invalid number format: \"%s\" - Using (-infinity, infinity)",
							integer));
			return makeTopValue();
		}
		Rational ratInt = Rational.valueOf(bigInt, BigInteger.ONE);
		return new IntervalValue(new Interval(ratInt), this, m_logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeRealValue(java.lang.String)
	 */
	@Override
	public IntervalValue makeRealValue(String real) {
		BigDecimal bigDec;
		try {
			bigDec = new BigDecimal(real);
		} catch (NumberFormatException e) {
			m_logger.warn(String
					.format("Invalid number format: \"%s\" - Using (-infinity, infinity)",
							real));
			return makeTopValue();
		}
		Rational lower = Rational.valueOf(
				bigDec.setScale(0, BigDecimal.ROUND_FLOOR).toBigInteger(),
				BigInteger.ONE);
		Rational upper = Rational.valueOf(
				bigDec.setScale(0, BigDecimal.ROUND_CEILING).toBigInteger(),
				BigInteger.ONE);
		return new IntervalValue(new Interval(lower, upper), this, m_logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeBoolValue(boolean)
	 */
	@Override
	public IntervalValue makeBoolValue(boolean bool) {
		return makeBottomValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeBitVectorValue
	 * (java.lang.String)
	 */
	public IntervalValue makeBitVectorValue(String bitvector) {
		return makeBottomValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeStringValue(java.lang.String)
	 */
	public IntervalValue makeStringValue(String value) {
		return makeBottomValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#valueIsCompatible
	 * (de.uni_freiburg.informatik
	 * .ultimate.plugins.analysis.abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean valueBelongsToDomainSystem(IAbstractValue<?> value) {
		return (value instanceof IntervalValue);
	}

}
