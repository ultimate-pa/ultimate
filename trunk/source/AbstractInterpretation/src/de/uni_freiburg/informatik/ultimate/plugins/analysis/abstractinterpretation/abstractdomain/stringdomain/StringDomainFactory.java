/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.stringdomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.stringdomain.StringValue.AIString;

/**
 * @author Christopher Dillo
 *
 */
public class StringDomainFactory implements IAbstractDomainFactory<AIString> {

	private static final String s_domainID = "STRING";
	
	private final Logger m_logger;

	public StringDomainFactory(Logger logger) {
		m_logger = logger;
	}
	
	public static String getDomainID() {
		return s_domainID;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeValue(java.lang.Object)
	 */
	@Override
	public StringValue makeValue(AIString value) {
		return new StringValue(value, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeTopValue()
	 */
	@Override
	public StringValue makeTopValue() {
		return new StringValue(AIString.TOP, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeBottomValue()
	 */
	@Override
	public StringValue makeBottomValue() {
		return new StringValue(AIString.BOTTOM, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeIntegerValue(java.lang.String)
	 */
	@Override
	public StringValue makeIntegerValue(String integer) {
		return new StringValue(AIString.TOP, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeRealValue(java.lang.String)
	 */
	@Override
	public StringValue makeRealValue(String real) {
		return new StringValue(AIString.TOP, this, m_logger);
	}

	/**
	 * @param value Given as a string to support arbitrarily large AIStrings.
	 * @return An abstract value representing the given AIString
	 */
	public StringValue makeStringValue(String value) {
		return new StringValue(AIString.TOP, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#getWideningOperator()
	 */
	@Override
	public StringMergeWideningOperator getWideningOperator() {
		return new StringMergeWideningOperator(this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#getMergeOperator()
	 */
	@Override
	public StringMergeWideningOperator getMergeOperator() {
		return new StringMergeWideningOperator(this, m_logger);
	}

}
