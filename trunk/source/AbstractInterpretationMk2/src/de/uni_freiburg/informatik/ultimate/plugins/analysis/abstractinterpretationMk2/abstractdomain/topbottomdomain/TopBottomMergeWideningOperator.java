/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.topbottomdomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.topbottomdomain.TopBottomValue.TopBottom;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IValueMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IValueWideningOperator;

/**
 * @author Christopher Dillo
 *
 */
public class TopBottomMergeWideningOperator implements IValueWideningOperator<TopBottom>,
		IValueMergeOperator<TopBottom> {
	
	private TopBottomValueFactory m_factory;
	
	private Logger m_logger;
	
	public TopBottomMergeWideningOperator(TopBottomValueFactory factory, Logger logger) {
		m_factory = factory;
		m_logger = logger;
	}

	public static String getName() {
		return "TOP-BOTTOM Merge & Widening";
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IWideningOperator#apply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractValue, de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue apply(IAbstractValue<?> oldValue, IAbstractValue<?> newValue) {
		TopBottomValue bvalA = (TopBottomValue) oldValue;
		TopBottomValue bvalB = (TopBottomValue) newValue; 
		
		// invalid state objects
		if ((bvalA == null) || (bvalB == null)) {
			return m_factory.makeTopValue();
		}
		
		TopBottom bvA = bvalA.getValue();
		TopBottom bvB = bvalB.getValue();
		
		if (bvA == bvB) return m_factory.makeValue(bvA);

		if ((bvA == TopBottom.TOP) || (bvB == TopBottom.TOP))
			return m_factory.makeTopValue();

		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IWideningOperator#copy()
	 */
	@Override
	public TopBottomMergeWideningOperator copy() {
		return new TopBottomMergeWideningOperator(m_factory, m_logger);
	}

}
