/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.paritydomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.paritydomain.ParityValue.Parity;

/**
 * @author Jan Hättig
 *
 */
public class ParityMergeWideningOperator implements
		IValueWideningOperator<Parity>, IValueMergeOperator<Parity> {

	private ParityValueFactory m_factory;

	private Logger m_logger;

	public ParityMergeWideningOperator(ParityValueFactory factory, Logger logger) {
		m_factory = factory;
		m_logger = logger;
	}

	public static String getName() {
		return "Parity Merge & Widening";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IWideningOperator#apply(de.uni_freiburg
	 * .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain
	 * .IAbstractValue, de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractValue)
	 */
	@Override
	public ParityValue apply(IAbstractValue<?> oldValue,
			IAbstractValue<?> newValue) {
		Parity oldV = (Parity) oldValue.getValue();
		Parity newV = (Parity) newValue.getValue();
		if ((oldV == null) || (newV == null))
			return m_factory.makeTopValue();

		// old is PLUSMINUS : PLUSMINUS
		if (oldValue.isTop())
			return m_factory.makeTopValue();

		// new is PLUSMINUS : PLUSMINUS
		if (newValue.isTop())
			return m_factory.makeTopValue();

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
		return m_factory.makeTopValue();
	}

	@Override
	public ParityMergeWideningOperator copy() {
		return new ParityMergeWideningOperator(m_factory, m_logger);
	}

}
