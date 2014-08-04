/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.intervaldomain;

import java.math.BigInteger;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;

/**
 * See "Principles of Program Analysis," page 228f
 * 
 * Given the set K of numbers found in the preferences and/or collected from literals in the RCFG.
 * 
 * [a, b] widen [x, y] = [LB_K(a, x), UB_K(b, y)]
 * 
 * LB_K(a, x) =
 * 	|	a			if	a <= x
 * 	|	k			if	(x < a) && (k = max({k in K | k <= x}))
 * 	|	-infinity	if	(x < a) && (for all k in K : x < k) 
 * 
 * UB_K(b, y) =
 * 	|	b			if	b >= y
 * 	|	k			if	(b < y) && (k = min({k in K | k >= y}))
 * 	|	+infinity	if	(b < y) && (for all k in K : y > k)
 * 
 * As in, use closest over-approximating bound in K or +-infinity if no such bound exists 
 * 
 * @author Christopher Dillo
 */
public class IntervalSetWideningOperator implements IWideningOperator<Interval> {
	
	private IntervalDomainFactory m_factory;
	
	private Logger m_logger;
	
	private List<Rational> m_numbersForWidening = new LinkedList<Rational>();
	
	public IntervalSetWideningOperator(IntervalDomainFactory factory, Set<String> numbersForWidening, Logger logger) {
		m_factory = factory;
		m_logger = logger;
		
		// get numbers as BigIntegers
		for (String s : numbersForWidening) {
			String[] number_with_frac = s.split("\\.");
			BigInteger trunc = new BigInteger(number_with_frac[0]);
			m_numbersForWidening.add(Rational.valueOf(trunc, BigInteger.ONE));
			// for real numbers r: If r has a fractional part, also add r rounded away from zero
			if (number_with_frac.length > 1) {
				BigInteger frac = new BigInteger(number_with_frac[1]);
				if (frac.signum() != 0) {
					if (trunc.signum() >= 0)
						m_numbersForWidening.add(Rational.valueOf(trunc.add(BigInteger.ONE), BigInteger.ONE));
					else
						m_numbersForWidening.add(Rational.valueOf(trunc.subtract(BigInteger.ONE), BigInteger.ONE));
				}
			}
		}
		Collections.sort(m_numbersForWidening);
	}
	
	public IntervalSetWideningOperator(IntervalDomainFactory factory, List<Rational> numbersForWidening, Logger logger) {
		m_factory = factory;
		m_logger = logger;
		m_numbersForWidening = numbersForWidening;
	}

	public static String getName() {
		return "Nearest In Set";
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator#apply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue, de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public IAbstractValue<Interval> apply(IAbstractValue<?> oldValue,
			IAbstractValue<?> newValue) {
		Interval oldV = (Interval) oldValue.getValue();
		Interval newV = (Interval) newValue.getValue();
		if ((oldV == null) || (newV == null)) return m_factory.makeTopValue();

		Rational lowerBound = LowerBoundInK(oldV.getLowerBound(), newV.getLowerBound());

		Rational upperBound = UpperBoundInK(oldV.getUpperBound(), newV.getUpperBound());

		Interval resultInterval = new Interval(lowerBound, upperBound);
		m_logger.debug(String.format("%s widen %s = %s", oldV, newV, resultInterval));
		return m_factory.makeValue(resultInterval);
	}
	
	/**
	 * LB_K(a, x) =
	 * 	|	a			if	a <= x
	 * 	|	k			if	(x < a) && (k = max({k in K | k <= x}))
	 * 	|	+infinity	if	(x < a) && (for all k in K : x < k) 
	 * @param oldLowerBound The lower bound of the old interval value
	 * @param newLowerBound The lower bound of the new interval value
	 * @return oldLowerBound, the nearest upper bound <= newLowerBound in K or negative infinity
	 */
	private Rational LowerBoundInK(Rational oldLowerBound, Rational newLowerBound) {
		if (oldLowerBound.compareTo(newLowerBound) <= 0)
			return oldLowerBound;
		
		// get max({k in K | k <= x})
		Rational maxK = null;
		for (Rational current : m_numbersForWidening) {
			if (current.compareTo(newLowerBound) > 0)
				break; // max found, leave loop
			maxK = current;
		}
		
		if ((maxK != null) && (maxK.compareTo(newLowerBound) <= 0))
			return maxK;
		
		// else: negative infinity
		return Rational.NEGATIVE_INFINITY;
	}
	
	/**
	 * UB_K(b, y) =
	 * 	|	b			if	b >= y
	 * 	|	k			if	(b < y) && (k = min({k in K | k >= y}))
	 * 	|	+infinity	if	(b < y) && (for all k in K : y > k)
	 * @param oldUpperBound The upper bound of the old interval value
	 * @param newUpperBound The upper bound of the new interval value
	 * @return oldUpperBound, the nearest lower bound >= newLowerBound in K or positive infinity
	 */
	private Rational UpperBoundInK(Rational oldUpperBound, Rational newUpperBound) {
		if (oldUpperBound.compareTo(newUpperBound) >= 0)
			return oldUpperBound;
		
		// get min({k in K | k >= y})
		Rational minK = null;
		for (Rational current : m_numbersForWidening) {
			minK = current;
			if (current.compareTo(newUpperBound) >= 0)
				break; // min found, leave loop
		}
		
		if ((minK != null) && (minK.compareTo(newUpperBound) >= 0))
			return minK;

		// else: positive infinity
		return Rational.POSITIVE_INFINITY;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator#copy()
	 */
	@Override
	public IWideningOperator<Interval> copy() {
		return new IntervalSetWideningOperator(m_factory, new LinkedList<Rational>(m_numbersForWidening), m_logger);
	}
}
