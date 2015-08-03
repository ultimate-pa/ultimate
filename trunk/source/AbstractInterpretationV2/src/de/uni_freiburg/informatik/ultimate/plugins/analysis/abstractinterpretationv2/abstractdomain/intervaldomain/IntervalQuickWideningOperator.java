/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.intervaldomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.valuedomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.valuedomain.IValueWideningOperator;

/**
 * @author Christopher Dillo
 *
 */
public class IntervalQuickWideningOperator implements IValueWideningOperator<Interval> {
	
	private IntervalValueFactory m_factory;
	
	private Logger m_logger;
	
	public IntervalQuickWideningOperator(IntervalValueFactory factory, Logger logger) {
		m_factory = factory;
		m_logger = logger;
	}

	public static String getName() {
		return "Quick (-infinity, infinity)";
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IWideningOperator#apply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue, de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractValue)
	 */
	@Override
	public IAbstractValue<Interval> apply(IAbstractValue<?> oldValue,
			IAbstractValue<?> newValue) {
		return m_factory.makeTopValue();
	}

	@Override
	public IntervalQuickWideningOperator copy() {
		return new IntervalQuickWideningOperator(m_factory, m_logger);
	}

}
