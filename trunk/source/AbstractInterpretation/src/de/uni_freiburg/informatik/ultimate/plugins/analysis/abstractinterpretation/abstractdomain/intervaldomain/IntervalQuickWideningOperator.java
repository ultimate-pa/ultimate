/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.intervaldomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;

/**
 * @author Christopher Dillo
 *
 */
public class IntervalQuickWideningOperator implements
		IWideningOperator<Interval> {
	
	private IntervalDomainFactory m_factory;
	
	@SuppressWarnings("unused")
	private Logger m_logger;
	
	public IntervalQuickWideningOperator(IntervalDomainFactory factory, Logger logger) {
		m_factory = factory;
		m_logger = logger;
	}

	public static String getName() {
		return "Interval Quick (-infinity, infinity)";
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator#apply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue, de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IAbstractValue<Interval> apply(IAbstractValue<?> oldValue,
			IAbstractValue<?> newValue) {
		return m_factory.makeTopValue();
	}

}
