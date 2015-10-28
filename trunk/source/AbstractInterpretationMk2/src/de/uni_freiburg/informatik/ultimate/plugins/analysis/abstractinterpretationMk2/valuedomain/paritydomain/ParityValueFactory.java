package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.paritydomain;

import java.math.BigInteger;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.paritydomain.ParityValue.Parity;


/**
 * @author Jan Hättig
 *
 */
public class ParityValueFactory implements IAbstractValueFactory<Parity> {

	private static final String s_domainID = "Parity";
	
	private final Logger m_logger;
	
	private IValueWideningOperator<Parity> m_wideningOperator;
	private IValueMergeOperator<Parity> m_mergeOperator;
	

	public ParityValueFactory(Logger logger) {
		m_logger = logger;		
	}
	
	public static String getDomainID() {
		return s_domainID;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomainFactory#makeValue()
	 */
	@Override
	public ParityValue makeValue(Parity value) {
		return new ParityValue(value, this, m_logger);
	}
	
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomainFactory#makeTopValue()
	 */
	@Override
	public ParityValue makeTopValue() {
		return new ParityValue(Parity.TOP, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomainFactory#makeBottomValue()
	 */
	@Override
	public ParityValue makeBottomValue() {
		return new ParityValue(Parity.EMPTY, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomainFactory#makeIntegerValue(int)
	 */
	@Override
	public ParityValue makeIntegerValue(String integer) {
		BigInteger number;
		try {
			number = new BigInteger(integer);
		} catch (NumberFormatException e) {
			m_logger.warn(String.format("Invalid number format: \"%s\" - Using Parity.BOTTOM", integer));
			return new ParityValue(Parity.TOP, this, m_logger);
		}
		
		BigInteger mod = number.mod(new BigInteger("2"));
		
		if (mod == BigInteger.ONE)
			return new ParityValue(Parity.ODD, this, m_logger);
		
		if (mod == BigInteger.ZERO)
			return new ParityValue(Parity.EVEN, this, m_logger);
		
		throw new RuntimeException();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomainFactory#makeIntegerValue(int)
	 */
	@Override
	public ParityValue makeRealValue(String real) {
		return makeTopValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomainFactory#makeBoolValue(boolean)
	 */
	@Override
	public ParityValue makeBoolValue(boolean bool) {
		return bool ? new ParityValue(Parity.ODD, this, m_logger) 
			: new ParityValue(Parity.EVEN, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomainFactory#makeBitVectorValue(java.lang.String)
	 */
	public ParityValue makeBitVectorValue(String bitvector) {
		return new ParityValue(Parity.TOP, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomainFactory#makeStringValue(java.lang.String)
	 */
	public ParityValue makeStringValue(String value) {
		return new ParityValue(Parity.TOP, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomainFactory#valueIsCompatible(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean valueBelongsToDomainSystem(IAbstractValue<?> value) {
		return (value instanceof ParityValue);
	}
}