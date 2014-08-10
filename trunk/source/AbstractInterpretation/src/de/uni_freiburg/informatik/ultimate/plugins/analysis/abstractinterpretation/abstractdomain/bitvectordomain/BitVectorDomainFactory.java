/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.bitvectordomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.bitvectordomain.BitVectorValue.BitVector;

/**
 * @author Christopher Dillo
 *
 */
public class BitVectorDomainFactory implements IAbstractDomainFactory<BitVector> {

	private static final String s_domainID = "BITVECTOR";
	
	private final Logger m_logger;

	public BitVectorDomainFactory(Logger logger) {
		m_logger = logger;
	}
	
	public static String getDomainID() {
		return s_domainID;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeValue(java.lang.Object)
	 */
	@Override
	public BitVectorValue makeValue(BitVector value) {
		return new BitVectorValue(value, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeTopValue()
	 */
	@Override
	public BitVectorValue makeTopValue() {
		return new BitVectorValue(BitVector.TOP, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeBottomValue()
	 */
	@Override
	public BitVectorValue makeBottomValue() {
		return new BitVectorValue(BitVector.BOTTOM, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeIntegerValue(java.lang.String)
	 */
	@Override
	public BitVectorValue makeIntegerValue(String integer) {
		return new BitVectorValue(BitVector.TOP, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeRealValue(java.lang.String)
	 */
	@Override
	public BitVectorValue makeRealValue(String real) {
		return new BitVectorValue(BitVector.TOP, this, m_logger);
	}

	/**
	 * @param bitvector Given as a string to support arbitrarily large BitVectors.
	 * @return An abstract value representing the given BitVector
	 */
	public BitVectorValue makeBitVectorValue(String bitvector) {
		return new BitVectorValue(BitVector.TOP, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#getWideningOperator()
	 */
	@Override
	public BitVectorMergeWideningOperator getWideningOperator() {
		return new BitVectorMergeWideningOperator(this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#getMergeOperator()
	 */
	@Override
	public BitVectorMergeWideningOperator getMergeOperator() {
		return new BitVectorMergeWideningOperator(this, m_logger);
	}

}
