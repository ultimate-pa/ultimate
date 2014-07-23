/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain.BoolValue.Bool;

/**
 * @author Christopher Dillo
 *
 */
public class BoolMergeWideningOperator implements IMergeOperator<BoolValue.Bool>,
		IWideningOperator<BoolValue.Bool> {
	
	private BoolDomainFactory m_factory;
	
	@SuppressWarnings("unused")
	private Logger m_logger;
	
	public BoolMergeWideningOperator(BoolDomainFactory factory, Logger logger) {
		m_factory = factory;
		m_logger = logger;
	}

	public static String getName() {
		return "BOOL Merge & Widening";
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator#apply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue, de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue apply(IAbstractValue<?> valueA, IAbstractValue<?> valueB) {
		BoolValue bvalA = (BoolValue) valueA;
		BoolValue bvalB = (BoolValue) valueB; 
		
		// invalid state objects
		if ((bvalA == null) || (bvalB == null)) {
			return null;
		}
		
		Bool boolA = bvalA.getValue();
		Bool boolB = bvalB.getValue();
		
		if (boolA == boolB) return m_factory.makeValue(boolA);

		if (boolA == Bool.EMPTY) {
			if (boolB == Bool.TRUE) return m_factory.makeValue(Bool.TRUE);
			if (boolB == Bool.FALSE) return m_factory.makeValue(Bool.FALSE);
		}
		if (boolB == Bool.EMPTY) {
			if (boolA == Bool.TRUE) return m_factory.makeValue(Bool.TRUE);
			if (boolA == Bool.FALSE) return m_factory.makeValue(Bool.FALSE);
		}
		
		return m_factory.makeValue(Bool.UNKNOWN);
	}

}
