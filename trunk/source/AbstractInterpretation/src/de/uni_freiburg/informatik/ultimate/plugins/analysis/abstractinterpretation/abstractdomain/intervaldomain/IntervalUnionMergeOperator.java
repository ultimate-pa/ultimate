/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.intervaldomain;

import java.math.BigInteger;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator;

/**
 * @author Christopher Dillo
 *
 */
public class IntervalUnionMergeOperator implements IMergeOperator<Interval> {
	
	private IntervalDomainFactory m_factory;
	
	@SuppressWarnings("unused")
	private Logger m_logger;
	
	public IntervalUnionMergeOperator(IntervalDomainFactory factory, Logger logger) {
		m_factory = factory;
		m_logger = logger;
	}

	public static String getName() {
		return "Interval Union";
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator#apply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue, de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IAbstractValue<Interval> apply(IAbstractValue<?> valueA, IAbstractValue<?> valueB) {
		/*
			[a, b] merge [x, y] => [min(a, x), max(b, y)]
		*/

		Interval intervalA = (Interval) valueA.getValue();
		Interval intervalB = (Interval) valueB.getValue();
		if ((intervalA == null) || (intervalB == null)) return m_factory.makeBottomValue();
		
		String resultLower, resultUpper;
		
		if (intervalA.lowerBoundIsNegInfty() || intervalB.lowerBoundIsNegInfty()) {
			resultLower = null;
		} else {
			BigInteger lA = new BigInteger(intervalA.getLowerBound());
			BigInteger lB = new BigInteger(intervalB.getLowerBound());
			if (lA.compareTo(lB) <= 0)
				resultLower = intervalA.getLowerBound();
			else
				resultLower = intervalB.getLowerBound();
		}
	
		if (intervalA.upperBoundIsPosInfty() || intervalB.upperBoundIsPosInfty()) {
			resultUpper = null;
		} else {
			BigInteger uA = new BigInteger(intervalA.getUpperBound());
			BigInteger uB = new BigInteger(intervalB.getUpperBound());
			if (uA.compareTo(uB) >= 0)
				resultUpper = intervalA.getUpperBound();
			else
				resultUpper = intervalB.getUpperBound();
		}
		
		return m_factory.makeValue(new Interval(resultLower, resultUpper));
	}

}
