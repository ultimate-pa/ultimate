/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain.SignValue.Sign;

/**
 * @author Christopher Dillo
 *
 */
public class SignMergeWideningOperator implements IWideningOperator<Sign>, IMergeOperator<Sign> {
	
	private SignDomainFactory m_factory;
	
	private Logger m_logger;
	
	public SignMergeWideningOperator(SignDomainFactory factory, Logger logger) {
		m_factory = factory;
		m_logger = logger;
	}

	public static String getName() {
		return "SIGN Merge & Widening";
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator#apply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue, de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue apply(IAbstractValue<?> oldValue, IAbstractValue<?> newValue) {
		Sign oldV = (Sign) oldValue.getValue();
		Sign newV = (Sign) newValue.getValue();
		if ((oldV == null) || (newV == null)) return m_factory.makeTopValue();

		// old is PLUSMINUS : PLUSMINUS
		if (oldValue.isTop())
			return m_factory.makeValue(Sign.PLUSMINUS);
		
		// new is PLUSMINUS : PLUSMINUS
		if (newValue.isTop())
			return m_factory.makeValue(Sign.PLUSMINUS);
		
		// old is ZERO : new
		if (oldValue.isBottom())
			return m_factory.makeValue(newV);

		// new is ZERO : old
		if (newValue.isBottom())
			return m_factory.makeValue(oldV);
		
		// old is new : old (or new)
		if (oldV == newV)
			return m_factory.makeValue(oldV);
		
		// old is PLUS, new is MINUS or vice versa : PLUSMINUS
		return m_factory.makeValue(Sign.PLUSMINUS);
	}

	@Override
	public SignMergeWideningOperator copy() {
		return new SignMergeWideningOperator(m_factory, m_logger);
	}

}
