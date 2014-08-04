/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.intervaldomain;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;

/**
 * @author Christopher Dillo
 *
 */
public class IntervalDomainFactory implements IAbstractDomainFactory<Interval> {
	
	private static final String s_domainID = "INTERVAL";
	
	private final Logger m_logger;
	private final String m_wideningOperatorName, m_mergeOperatorName;
	
	private final Set<String> m_numbersForWidening;
	
	private IWideningOperator<Interval> m_wideningOperator = null;

	public IntervalDomainFactory(Logger logger, Set<String> numbersForWidening, String wideningOperatorName, String mergeOperatorName) {
		m_logger = logger;
		m_numbersForWidening = numbersForWidening;
		m_wideningOperatorName = wideningOperatorName;
		m_mergeOperatorName = mergeOperatorName;
	}
	
	public static String getDomainID() {
		return s_domainID;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeValue(java.lang.Object)
	 */
	@Override
	public IntervalValue makeValue(Interval value) {
		return new IntervalValue(value, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeTopValue()
	 */
	@Override
	public IntervalValue makeTopValue() {
		return new IntervalValue(new Interval(Rational.NEGATIVE_INFINITY, Rational.POSITIVE_INFINITY), this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeBottomValue()
	 */
	@Override
	public IntervalValue makeBottomValue() {
		return new IntervalValue(new Interval(), this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeIntegerValue(java.lang.String)
	 */
	@Override
	public IntervalValue makeIntegerValue(String integer) {
		BigInteger bigInt;
		try {
			bigInt = new BigInteger(integer);
		} catch (NumberFormatException e) {
			m_logger.warn(String.format("Invalid number format: \"%s\" - Using (-infinity, infinity)", integer));
			return makeTopValue();
		}
		Rational ratInt = Rational.valueOf(bigInt, BigInteger.ONE);
		return new IntervalValue(new Interval(ratInt), this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeRealValue(java.lang.String)
	 */
	@Override
	public IntervalValue makeRealValue(String real) {
		BigDecimal bigDec;
		try {
			bigDec = new BigDecimal(real);
		} catch (NumberFormatException e) {
			m_logger.warn(String.format("Invalid number format: \"%s\" - Using (-infinity, infinity)", real));
			return makeTopValue();
		}
		Rational lower = Rational.valueOf(bigDec.setScale(0, BigDecimal.ROUND_FLOOR).toBigInteger(), BigInteger.ONE);
		Rational upper = Rational.valueOf(bigDec.setScale(0, BigDecimal.ROUND_CEILING).toBigInteger(), BigInteger.ONE);
		return new IntervalValue(new Interval(lower, upper), this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#getWideningOperator()
	 */
	@Override
	public IWideningOperator<Interval> getWideningOperator() {
		if (m_wideningOperator == null)
			m_wideningOperator = makeWideningOperator();
		return m_wideningOperator.copy();
	}
	
	private IWideningOperator<Interval> makeWideningOperator() {
		if (m_wideningOperatorName.equals(IntervalQuickWideningOperator.getName()))
			return new IntervalQuickWideningOperator(this, m_logger);

		if (m_wideningOperatorName.equals(IntervalIntWideningOperator.getName()))
			return new IntervalIntWideningOperator(this, m_numbersForWidening, m_logger);

		if (m_wideningOperatorName.equals(IntervalSetWideningOperator.getName()))
			return new IntervalSetWideningOperator(this, m_numbersForWidening, m_logger);
		
		// default: IntervalQuickWideningOperator
		m_logger.warn(String.format("Unknown Interval widening operator \"%s\" chosen, using \"%s\" instead",
				m_mergeOperatorName, IntervalQuickWideningOperator.getName()));
		return new IntervalQuickWideningOperator(this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#getMergeOperator()
	 */
	@Override
	public IMergeOperator<Interval> getMergeOperator() {
		if (m_mergeOperatorName.equals(IntervalUnionMergeOperator.getName()))
			return new IntervalUnionMergeOperator(this, m_logger);
		
		// default: IntervalUnionMergeOperator
		m_logger.warn(String.format("Unknown Interval merge operator \"%s\" chosen, using \"%s\" instead",
				m_mergeOperatorName, IntervalUnionMergeOperator.getName()));
		return new IntervalUnionMergeOperator(this, m_logger);
	}

}
