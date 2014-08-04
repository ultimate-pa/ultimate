/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.intervaldomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator;

/**
 * @author Christopher Dillo
 *
 */
public class IntervalUnionMergeOperator implements IMergeOperator<Interval> {
	
	private IntervalDomainFactory m_factory;
	
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

		Rational lA = intervalA.getLowerBound();
		Rational uA = intervalA.getUpperBound();
		Rational lB = intervalB.getLowerBound();
		Rational uB = intervalB.getUpperBound();
		
		Rational resultLower = (lA.compareTo(lB) < 0) ? lA : lB;

		Rational resultUpper = (uA.compareTo(uB) > 0) ? uA : uB;
		
		return m_factory.makeValue(new Interval(resultLower, resultUpper));
	}

	@Override
	public IntervalUnionMergeOperator copy() {
		return new IntervalUnionMergeOperator(m_factory, m_logger);
	}

}
