/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractDomainRegistry;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain.SignValue.Sign;

/**
 * @author Christopher Dillo
 *
 */
public class SignDomainFactory implements IAbstractDomainFactory<SignValue.Sign> {

	private static final String s_domainID = "SIGN";
	
	private Logger m_logger;
	
	private AbstractDomainRegistry m_domainRegistry;
	
	private IWideningOperator<SignValue.Sign> m_wideningOp;
	private IMergeOperator<SignValue.Sign> m_mergeOp;

	@SuppressWarnings("unchecked")
	public SignDomainFactory(Logger logger, AbstractDomainRegistry domainRegistry, String wideningOperatorName, String mergeOperatorName) {
		m_logger = logger;
		m_domainRegistry = domainRegistry;
		
		// create widening operator
		IWideningOperator<?> wideningOp;
		try {
			wideningOp = m_domainRegistry.getWideningOperator(getDomainID(), wideningOperatorName).
					getConstructor(SignDomainFactory.class, Logger.class).newInstance(this, m_logger);
			m_wideningOp = (IWideningOperator<SignValue.Sign>) wideningOp;
		} catch (Exception e) {
			m_logger.warn(String.format("Invalid widening operator %s chosen for the %s domain, using default operator %s",
					wideningOperatorName, s_domainID, SignMergeWideningOperator.getName()));
			m_wideningOp = new SignMergeWideningOperator(this, m_logger); // fallback
		}
		
		// create merge operator
		IMergeOperator<?> mergeOp;
		try {
			mergeOp = m_domainRegistry.getMergeOperator(getDomainID(), mergeOperatorName).
					getConstructor(SignDomainFactory.class, Logger.class).newInstance(this, m_logger);
			m_mergeOp = (IMergeOperator<SignValue.Sign>) mergeOp;
		} catch (Exception e) {
			m_logger.warn(String.format("Invalid merge operator %s chosen for the %s domain, using default operator %s",
					mergeOperatorName, s_domainID, SignMergeWideningOperator.getName()));
			m_mergeOp = new SignMergeWideningOperator(this, m_logger); // fallback
		}
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
		// TODO: Representation of integers as a string??
		
		if (integer.equals("0"))
			return new SignValue(Sign.ZERO, this, m_logger);
		
		if (integer.startsWith("-"))
			return new SignValue(Sign.MINUS, this, m_logger);
		
		return new SignValue(Sign.PLUS, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeIntegerValue(int)
	 */
	@Override
	public SignValue makeRealValue(String real) {
		// TODO: Representation of reals as a string??
		
		if (real.equals("0"))
			return new SignValue(Sign.ZERO, this, m_logger);
		
		if (real.startsWith("-"))
			return new SignValue(Sign.MINUS, this, m_logger);
		
		return new SignValue(Sign.PLUS, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeWideningOperator()
	 */
	@Override
	public IWideningOperator<SignValue.Sign> getWideningOperator() {
		return m_wideningOp;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeMergeOperator()
	 */
	@Override
	public IMergeOperator<SignValue.Sign> getMergeOperator() {
		return m_mergeOp;
	}

}
