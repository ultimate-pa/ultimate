/*
 * Copyright (C) 2014-2015 Christopher Dillo
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AbstractInterpretation plug-in.
 * 
 * The ULTIMATE AbstractInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AbstractInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AbstractInterpretation plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.intervaldomain;

import java.math.BigInteger;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;

/**
 * See "Principles of Program Analysis," page 225f
 * 
 * Given an interval [m, n], here derived as [min(K), max(K)] of the set K of numbers
 * found in the preferences and/or collected from literals in the RCFG.
 * 
 * [a, b] widen [x, y] =
 * 	|	[a, b] union [x, y]		if	([a, b] sub [m, n]) or ([x, y] sub [a, b])
 * 	|	(-infinity, +infinity)	otherwise
 * 
 * @author Christopher Dillo
 */
public class IntervalIntWideningOperator implements IWideningOperator<Interval> {
	
	private IntervalDomainFactory m_factory;
	
	private Logger m_logger;
	
	private final IntervalValue m_bounds;
	
	public IntervalIntWideningOperator(IntervalDomainFactory factory, Set<String> numbersForWidening, Logger logger) {
		m_factory = factory;
		m_logger = logger;
		
		// get min and max of numbersForWidening for [m, n]
		BigInteger minInt = null;
		BigInteger maxInt = null;
		for (String s : numbersForWidening) {
			// take floor of real values
			BigInteger currentInt = null;
			try {
				currentInt = new BigInteger(s.split("\\.")[0]);
			} catch (NumberFormatException e) {
				m_logger.warn(String.format("Invalid number string: \"%s\"", s));
			}
			
			if (currentInt != null) {
				if ((minInt == null) || (currentInt.compareTo(minInt) < 0))
					minInt = currentInt;
				if ((maxInt == null) || (currentInt.compareTo(maxInt) > 0))
					maxInt = currentInt;
			}
		}
		if ((minInt == null) || (maxInt == null)) {
			m_bounds = m_factory.makeBottomValue();
		} else {
			Rational minRat = Rational.valueOf(minInt, BigInteger.ONE);
			Rational maxRat = Rational.valueOf(maxInt, BigInteger.ONE);
			m_bounds = m_factory.makeValue(new Interval(minRat, maxRat));
		}
		m_logger.debug(String.format("WIDEN WITH BOUNDS [%s, %s]", minInt.toString(), maxInt.toString()));
	}
	
	public IntervalIntWideningOperator(IntervalDomainFactory factory, IntervalValue bounds, Logger logger) {
		m_factory = factory;
		m_logger = logger;
		m_bounds =  bounds;
	}

	public static String getName() {
		return "Keep within Interval";
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
		
		if (oldValue.isSub(newValue)) {
			m_logger.debug(String.format("%s widen %s = %s", oldV, newV, oldV));
			return m_factory.makeValue(oldV);
		}
		
		if (oldValue.isSub(m_bounds)) {
			// merge oldV and newV
			Rational lA = oldV.getLowerBound();
			Rational uA = oldV.getUpperBound();
			Rational lB = newV.getLowerBound();
			Rational uB = newV.getUpperBound();
			
			Rational resultLower = (lA.compareTo(lB) < 0) ? lA : lB;

			Rational resultUpper = (uA.compareTo(uB) > 0) ? uA : uB;
			
			Interval resultInterval = new Interval(resultLower, resultUpper);
			m_logger.debug(String.format("%s widen %s = %s", oldV, newV, resultInterval));
			return m_factory.makeValue(resultInterval);
		}

		IntervalValue result = m_factory.makeTopValue();
		m_logger.debug(String.format("%s widen %s = %s", oldV, newV, result.getValue()));
		return result;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator#copy()
	 */
	@Override
	public IWideningOperator<Interval> copy() {
		return new IntervalIntWideningOperator(m_factory, m_bounds.copy(), m_logger);
	}

}
