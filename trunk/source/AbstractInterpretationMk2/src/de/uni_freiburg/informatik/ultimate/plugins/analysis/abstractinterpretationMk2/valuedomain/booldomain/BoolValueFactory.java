/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.booldomain;

import java.math.BigDecimal;
import java.math.BigInteger;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.booldomain.BoolValue.Bool;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValueFactory;

/**
 * @author Christopher Dillo
 *
 */
public class BoolValueFactory implements IAbstractValueFactory<Bool> {

	private static final String s_DomainID = "BOOL";

	private Logger m_logger;

	public BoolValueFactory(Logger logger) {
		m_logger = logger;
	}

	public static String getDomainID() {
		return s_DomainID;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeValue()
	 */
	@Override
	public BoolValue makeValue(Bool value) {
		return new BoolValue(value, this, m_logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeTopValue()
	 */
	@Override
	public BoolValue makeTopValue() {
		return new BoolValue(Bool.UNKNOWN, this, m_logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeBottomValue()
	 */
	@Override
	public BoolValue makeBottomValue() {
		return new BoolValue(Bool.EMPTY, this, m_logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeIntegerValue(java.lang.String)
	 */
	@Override
	public BoolValue makeIntegerValue(String integer) {
		BigInteger number;
		try {
			number = new BigInteger(integer);
		} catch (NumberFormatException e) {
			m_logger.warn(String.format(
					"Invalid number format: \"%s\" - Using Bool.UNKNOWN",
					integer));
			return new BoolValue(Bool.UNKNOWN, this, m_logger);
		}

		if (number.equals(BigInteger.ZERO))
			return new BoolValue(Bool.FALSE, this, m_logger);

		return new BoolValue(Bool.TRUE, this, m_logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeRealValue(java.lang.String)
	 */
	@Override
	public BoolValue makeRealValue(String real) {
		BigDecimal number;
		try {
			number = new BigDecimal(real);
		} catch (NumberFormatException e) {
			m_logger.warn(String.format(
					"Invalid number format: \"%s\" - Using Bool.UNKNOWN", real));
			return new BoolValue(Bool.UNKNOWN, this, m_logger);
		}

		if (number.signum() == 0)
			return new BoolValue(Bool.FALSE, this, m_logger);

		return new BoolValue(Bool.TRUE, this, m_logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeBoolValue(boolean)
	 */
	@Override
	public BoolValue makeBoolValue(boolean bool) {
		return new BoolValue(bool ? Bool.TRUE : Bool.FALSE, this, m_logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeBitVectorValue
	 * (java.lang.String)
	 */
	public BoolValue makeBitVectorValue(String bitvector) {
		return makeBottomValue();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeStringValue(java.lang.String)
	 */
	public BoolValue makeStringValue(String value) {
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
		return (value instanceof BoolValue);
	}
}
