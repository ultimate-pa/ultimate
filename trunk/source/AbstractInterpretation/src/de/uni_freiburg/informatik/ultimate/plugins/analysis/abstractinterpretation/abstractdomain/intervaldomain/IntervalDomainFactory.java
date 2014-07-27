/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.intervaldomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractDomainRegistry;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;

/**
 * @author Christopher Dillo
 *
 */
public class IntervalDomainFactory implements IAbstractDomainFactory<Interval> {
	
	private static final String s_domainID = "INTERVAL";
	
	private Logger m_logger;
	
	private AbstractDomainRegistry m_domainRegistry;
	
	private IWideningOperator<Interval> m_wideningOp;
	private IMergeOperator<Interval> m_mergeOp;

	@SuppressWarnings("unchecked")
	public IntervalDomainFactory(Logger logger, AbstractDomainRegistry domainRegistry, String wideningOperatorName, String mergeOperatorName) {
		m_logger = logger;
		m_domainRegistry = domainRegistry;
		
		// create widening operator
		IWideningOperator<?> wideningOp;
		try {
			wideningOp = m_domainRegistry.getWideningOperator(getDomainID(), wideningOperatorName).
					getConstructor(IntervalDomainFactory.class, Logger.class).newInstance(this, m_logger);
			m_wideningOp = (IWideningOperator<Interval>) wideningOp;
		} catch (Exception e) {
			/*m_logger.warn(String.format("Invalid widening operator %s chosen for the %s domain, using default operator %s",
					wideningOperatorName, s_domainID, SignMergeWideningOperator.getName()));
			m_wideningOp = new SignMergeWideningOperator(this, m_logger); // fallback */ // TODO: !!!
		}
		
		// create merge operator
		IMergeOperator<?> mergeOp;
		try {
			mergeOp = m_domainRegistry.getMergeOperator(getDomainID(), mergeOperatorName).
					getConstructor(IntervalDomainFactory.class, Logger.class).newInstance(this, m_logger);
			m_mergeOp = (IMergeOperator<Interval>) mergeOp;
		} catch (Exception e) {
			/*m_logger.warn(String.format("Invalid merge operator %s chosen for the %s domain, using default operator %s",
					mergeOperatorName, s_domainID, SignMergeWideningOperator.getName()));
			m_mergeOp = new SignMergeWideningOperator(this, m_logger); // fallback */ // TODO: !!!
		}
	}
	
	public static String getDomainID() {
		return s_domainID;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeValue(java.lang.Object)
	 */
	@Override
	public IAbstractValue<Interval> makeValue(Interval value) {
		return new IntervalValue(value, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeTopValue()
	 */
	@Override
	public IAbstractValue<Interval> makeTopValue() {
		return new IntervalValue(new Interval(null, null), this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeBottomValue()
	 */
	@Override
	public IAbstractValue<Interval> makeBottomValue() {
		return new IntervalValue(new Interval(), this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeIntegerValue(java.lang.String)
	 */
	@Override
	public IAbstractValue<Interval> makeIntegerValue(String integer) {
		return new IntervalValue(new Interval(integer, integer), this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeRealValue(java.lang.String)
	 */
	@Override
	public IAbstractValue<Interval> makeRealValue(String real) {
		return new IntervalValue(new Interval(real, real), this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#getWideningOperator()
	 */
	@Override
	public IWideningOperator<Interval> getWideningOperator() {
		return m_wideningOp;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#getMergeOperator()
	 */
	@Override
	public IMergeOperator<Interval> getMergeOperator() {
		return m_mergeOp;
	}

}
