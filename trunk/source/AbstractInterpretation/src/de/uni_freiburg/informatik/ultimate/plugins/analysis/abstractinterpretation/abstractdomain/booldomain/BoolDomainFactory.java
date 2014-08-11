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

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeBoolValue(boolean)
	 */
	@Override
	public BoolValue makeBoolValue(boolean bool) {
		return new BoolValue(bool ? Bool.TRUE : Bool.FALSE, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeBitVectorValue(java.lang.String)
	 */
	public BoolValue makeBitVectorValue(String bitvector) {
		return makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeStringValue(java.lang.String)
	 */
	public BoolValue makeStringValue(String value) {
		return makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#valueIsCompatible(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean valueBelongsToDomainSystem(IAbstractValue<?> value) {
		return (value instanceof BoolValue);
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
