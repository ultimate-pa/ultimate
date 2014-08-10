/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.stringdomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.stringdomain.StringValue.AIString;

/**
 * @author Christopher Dillo
 *
 */
public class StringMergeWideningOperator implements IWideningOperator<AIString>,
		IMergeOperator<AIString> {
	
	private StringDomainFactory m_factory;
	
	private Logger m_logger;
	
	public StringMergeWideningOperator(StringDomainFactory factory, Logger logger) {
		m_factory = factory;
		m_logger = logger;
	}

	public static String getName() {
		return "AIString Merge & Widening";
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator#apply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue, de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public StringValue apply(IAbstractValue<?> oldValue, IAbstractValue<?> newValue) {
		StringValue bvalA = (StringValue) oldValue;
		StringValue bvalB = (StringValue) newValue; 
		
		// invalid state objects
		if ((bvalA == null) || (bvalB == null)) {
			return m_factory.makeTopValue();
		}
		
		AIString bvA = bvalA.getValue();
		AIString bvB = bvalB.getValue();
		
		if (bvA == bvB) return m_factory.makeValue(bvA);

		if ((bvA == AIString.TOP) || (bvB == AIString.TOP))
			return m_factory.makeTopValue();

		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator#copy()
	 */
	@Override
	public StringMergeWideningOperator copy() {
		return new StringMergeWideningOperator(m_factory, m_logger);
	}

}
