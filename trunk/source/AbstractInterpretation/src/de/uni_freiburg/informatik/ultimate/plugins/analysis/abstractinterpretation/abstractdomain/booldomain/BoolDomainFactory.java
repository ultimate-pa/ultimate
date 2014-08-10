/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain;

import java.math.BigDecimal;
import java.math.BigInteger;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain.BoolValue.Bool;

/**
 * @author Christopher Dillo
 *
 */
public class BoolDomainFactory implements IAbstractDomainFactory<Bool> {

	private static final String s_DomainID = "BOOL";
	
	private Logger m_logger;
	
	public BoolDomainFactory(Logger logger) {
		m_logger = logger;
	}

	public static String getDomainID() {
		return s_DomainID;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeValue()
	 */
	@Override
	public BoolValue makeValue(Bool value) {
		return new BoolValue(value, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeTopValue()
	 */
	@Override
	public BoolValue makeTopValue() {
		return new BoolValue(Bool.UNKNOWN, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeBottomValue()
	 */
	@Override
	public BoolValue makeBottomValue() {
		return new BoolValue(Bool.EMPTY, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeIntegerValue(java.lang.String)
	 */
	@Override
	public BoolValue makeIntegerValue(String integer) {
		BigInteger number;
		try {
			number = new BigInteger(integer);
		} catch (NumberFormatException e) {
			m_logger.warn(String.format("Invalid number format: \"%s\" - Using Bool.UNKNOWN", integer));
			return new BoolValue(Bool.UNKNOWN, this, m_logger);
		}
		
		if (number.equals(BigInteger.ZERO))
			return new BoolValue(Bool.FALSE, this, m_logger);
		
		return new BoolValue(Bool.TRUE, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeRealValue(java.lang.String)
	 */
	@Override
	public BoolValue makeRealValue(String real) {
		BigDecimal number;
		try {
			number = new BigDecimal(real);
		} catch (NumberFormatException e) {
			m_logger.warn(String.format("Invalid number format: \"%s\" - Using Bool.UNKNOWN", real));
			return new BoolValue(Bool.UNKNOWN, this, m_logger);
		}
		
		if (number.signum() == 0)
			return new BoolValue(Bool.FALSE, this, m_logger);
		
		return new BoolValue(Bool.TRUE, this, m_logger);
	}
	
	/**
	 * @param bool
	 * @return A BoolValue based on a given boolean value (true or false)
	 */
	public BoolValue makeBooleanValue(boolean bool) {
		return new BoolValue(bool ? Bool.TRUE : Bool.FALSE, this, m_logger);
	}
	
	/**
	 * For use with values generated from IAbstractValue's comparison operators
	 * @param value An abstract value to get a boolean value for
	 * @return A copy of the value if it is a BoolValue, otherwise FALSE, if the given value is bottom; else true
	 */
	public BoolValue makeFromAbstractValue(IAbstractValue<?> value) {
		if (value instanceof BoolValue) return (BoolValue) value.copy();
		
		return new BoolValue(value.isBottom() ? Bool.FALSE : Bool.TRUE, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeWideningOperator()
	 */
	@Override
	public IWideningOperator<BoolValue.Bool> getWideningOperator() {
		return new BoolMergeWideningOperator(this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeMergeOperator()
	 */
	@Override
	public IMergeOperator<BoolValue.Bool> getMergeOperator() {
		return new BoolMergeWideningOperator(this, m_logger);
	}

}
