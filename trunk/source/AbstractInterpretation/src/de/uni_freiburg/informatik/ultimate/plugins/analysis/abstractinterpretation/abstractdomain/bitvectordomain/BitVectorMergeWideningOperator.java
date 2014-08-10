/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.bitvectordomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.bitvectordomain.BitVectorValue.BitVector;

/**
 * @author Christopher Dillo
 *
 */
public class BitVectorMergeWideningOperator implements IWideningOperator<BitVector>,
		IMergeOperator<BitVector> {
	
	private BitVectorDomainFactory m_factory;
	
	private Logger m_logger;
	
	public BitVectorMergeWideningOperator(BitVectorDomainFactory factory, Logger logger) {
		m_factory = factory;
		m_logger = logger;
	}

	public static String getName() {
		return "BITVECTOR Merge & Widening";
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator#apply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue, de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BitVectorValue apply(IAbstractValue<?> oldValue, IAbstractValue<?> newValue) {
		BitVectorValue bvalA = (BitVectorValue) oldValue;
		BitVectorValue bvalB = (BitVectorValue) newValue; 
		
		// invalid state objects
		if ((bvalA == null) || (bvalB == null)) {
			return m_factory.makeTopValue();
		}
		
		BitVector bvA = bvalA.getValue();
		BitVector bvB = bvalB.getValue();
		
		if (bvA == bvB) return m_factory.makeValue(bvA);

		if ((bvA == BitVector.TOP) || (bvB == BitVector.TOP))
			return m_factory.makeTopValue();

		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator#copy()
	 */
	@Override
	public BitVectorMergeWideningOperator copy() {
		return new BitVectorMergeWideningOperator(m_factory, m_logger);
	}

}
