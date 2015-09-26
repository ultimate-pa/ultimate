/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.topbottomdomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IValueMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IValueWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.signdomain.SignValue.Sign;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.topbottomdomain.TopBottomValue.TopBottom;

/**
 * Simplest domain consisting of TOP and BOTTOM only. Created to be used with
 * data types like BitVector and String, which do not have their own domain
 * systems.
 * 
 * @author Christopher Dillo
 */
public class TopBottomValueFactory implements IAbstractValueFactory<TopBottom> {

	private static final String s_domainID = "TOP-BOTTOM";

	private final Logger m_logger;

	public TopBottomValueFactory(Logger logger) {
		m_logger = logger;
	}

	public static String getDomainID() {
		return s_domainID;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeValue(java.lang.Object)
	 */
	@Override
	public TopBottomValue makeValue(TopBottom value) {
		return new TopBottomValue(value, this, m_logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeTopValue()
	 */
	@Override
	public TopBottomValue makeTopValue() {
		return new TopBottomValue(TopBottom.TOP, this, m_logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeBottomValue()
	 */
	@Override
	public TopBottomValue makeBottomValue() {
		return new TopBottomValue(TopBottom.BOTTOM, this, m_logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeIntegerValue(java.lang.String)
	 */
	@Override
	public TopBottomValue makeIntegerValue(String integer) {
		return new TopBottomValue(TopBottom.TOP, this, m_logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeRealValue(java.lang.String)
	 */
	@Override
	public TopBottomValue makeRealValue(String real) {
		return new TopBottomValue(TopBottom.TOP, this, m_logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeBoolValue(boolean)
	 */
	@Override
	public TopBottomValue makeBoolValue(boolean bool) {
		return new TopBottomValue(TopBottom.TOP, this, m_logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeBitVectorValue
	 * (java.lang.String)
	 */
	public TopBottomValue makeBitVectorValue(String bitvector) {
		return new TopBottomValue(TopBottom.TOP, this, m_logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#makeStringValue(java.lang.String)
	 */
	public TopBottomValue makeStringValue(String value) {
		return new TopBottomValue(TopBottom.BOTTOM, this, m_logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#valueIsCompatible
	 * (de.uni_freiburg.informatik
	 * .ultimate.plugins.analysis.abstractinterpretationMk2
	 * .abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean valueBelongsToDomainSystem(IAbstractValue<?> value) {
		return (value instanceof TopBottomValue);
	}

}
