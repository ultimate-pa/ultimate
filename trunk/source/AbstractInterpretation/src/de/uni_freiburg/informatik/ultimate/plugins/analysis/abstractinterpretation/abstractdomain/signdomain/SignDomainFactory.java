/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain;

import java.math.BigDecimal;
import java.math.BigInteger;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain.SignValue.Sign;

/**
 * @author Christopher Dillo
 *
 */
public class SignDomainFactory implements IAbstractDomainFactory<Sign> {

	private static final String s_domainID = "SIGN";
	
	private final Logger m_logger;
	
	private final String m_wideningOperatorName, m_mergeOperatorName;

	public SignDomainFactory(Logger logger, String wideningOperatorName, String mergeOperatorName) {
		m_logger = logger;
		m_wideningOperatorName = wideningOperatorName;
		m_mergeOperatorName = mergeOperatorName;
	}
	
	public static String getDomainID() {
		return s_domainID;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeValue()
	 */
	@Override
	public SignValue makeValue(Sign value) {
		return new SignValue(value, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeTopValue()
	 */
	@Override
	public SignValue makeTopValue() {
		return new SignValue(Sign.PLUSMINUS, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeBottomValue()
	 */
	@Override
	public SignValue makeBottomValue() {
		return new SignValue(Sign.ZERO, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeIntegerValue(int)
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
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeIntegerValue(int)
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
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeWideningOperator()
	 */
	@Override
	public IWideningOperator<SignValue.Sign> getWideningOperator() {
		if (m_wideningOperatorName.equals(SignMergeWideningOperator.getName()))
			return new SignMergeWideningOperator(this, m_logger);
		
		// default: SignMergeWideningOperator
		m_logger.warn(String.format("Unknown Sign widening operator \"%s\" chosen, using \"%s\" instead",
				m_mergeOperatorName, SignMergeWideningOperator.getName()));
		return new SignMergeWideningOperator(this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeMergeOperator()
	 */
	@Override
	public IMergeOperator<SignValue.Sign> getMergeOperator() {
		if (m_mergeOperatorName.equals(SignMergeWideningOperator.getName()))
			return new SignMergeWideningOperator(this, m_logger);
		
		// default: SignMergeWideningOperator
		m_logger.warn(String.format("Unknown Sign merge operator \"%s\" chosen, using \"%s\" instead",
				m_mergeOperatorName, SignMergeWideningOperator.getName()));
		return new SignMergeWideningOperator(this, m_logger);
	}

}
