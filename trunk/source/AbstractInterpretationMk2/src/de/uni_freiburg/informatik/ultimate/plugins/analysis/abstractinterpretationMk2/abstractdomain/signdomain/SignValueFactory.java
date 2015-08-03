/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.signdomain;

import java.math.BigDecimal;
import java.math.BigInteger;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.booldomain.BoolValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.booldomain.BoolValue.Bool;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.intervaldomain.Interval;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.intervaldomain.IntervalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.signdomain.SignValue.Sign;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IValueMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IValueWideningOperator;

/**
 * @author Christopher Dillo
 *
 */
public class SignValueFactory implements IAbstractValueFactory<Sign> {

	private static final String s_domainID = "SIGN";
	
	private final Logger m_logger;
	
	private IValueWideningOperator<Sign> m_wideningOperator;
	private IValueMergeOperator<Sign> m_mergeOperator;
	

	public SignValueFactory(Logger logger) {
		m_logger = logger;		
	}
	
	public static String getDomainID() {
		return s_domainID;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomainFactory#makeValue()
	 */
	@Override
	public SignValue makeValue(Sign value) {
		return new SignValue(value, this, m_logger);
	}
	
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomainFactory#makeTopValue()
	 */
	@Override
	public SignValue makeTopValue() {
		return new SignValue(Sign.PLUSMINUS, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomainFactory#makeBottomValue()
	 */
	@Override
	public SignValue makeBottomValue() {
		return new SignValue(Sign.ZERO, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomainFactory#makeIntegerValue(int)
	 */
	@Override
	public SignValue makeIntegerValue(String integer) {
		BigInteger number;
		try {
			number = new BigInteger(integer);
		} catch (NumberFormatException e) {
			m_logger.warn(String.format("Invalid number format: \"%s\" - Using Sign.PLUSMINUS", integer));
			return new SignValue(Sign.PLUSMINUS, this, m_logger);
		}
		
		int signum = number.signum();
		
		if (signum == 0)
			return new SignValue(Sign.ZERO, this, m_logger);
		
		if (signum < 0)
			return new SignValue(Sign.MINUS, this, m_logger);
		
		return new SignValue(Sign.PLUS, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomainFactory#makeIntegerValue(int)
	 */
	@Override
	public SignValue makeRealValue(String real) {
		BigDecimal number;
		try {
			number = new BigDecimal(real);
		} catch (NumberFormatException e) {
			m_logger.warn(String.format("Invalid number format: \"%s\" - Using Sign.PLUSMINUS", real));
			return new SignValue(Sign.PLUSMINUS, this, m_logger);
		}
		
		int signum = number.signum();
		
		if (signum == 0)
			return new SignValue(Sign.ZERO, this, m_logger);
		
		if (signum < 0)
			return new SignValue(Sign.MINUS, this, m_logger);
		
		return new SignValue(Sign.PLUS, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomainFactory#makeBoolValue(boolean)
	 */
	@Override
	public SignValue makeBoolValue(boolean bool) {
		return new SignValue(Sign.EMPTY, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomainFactory#makeBitVectorValue(java.lang.String)
	 */
	public SignValue makeBitVectorValue(String bitvector) {
		return new SignValue(Sign.EMPTY, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomainFactory#makeStringValue(java.lang.String)
	 */
	public SignValue makeStringValue(String value) {
		return new SignValue(Sign.EMPTY, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomainFactory#valueIsCompatible(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean valueBelongsToDomainSystem(IAbstractValue<?> value) {
		return (value instanceof SignValue);
	}	
}
