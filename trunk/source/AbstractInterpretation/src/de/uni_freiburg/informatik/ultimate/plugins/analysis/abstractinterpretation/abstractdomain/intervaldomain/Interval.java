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

import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * An integer interval [l, u] with l <= u
 * (-infinity, infinity), (-infinity, u], [l, infinity) are also allowed
 * l and u are stored as Rational. If l > u, the interval is empty.
 * 
 * @author Christopher Dillo
 */
public class Interval {	
	private Rational m_lower, m_upper;
	
	/**
	 * [lowerBound, upperBound] lowerBound <= upperBound
	 * @param lowerBound Rational for the lower bound
	 * @param upperBound Rational for the upper bound
	 */
	public Interval(Rational lowerBound, Rational upperBound) {
		m_lower = lowerBound.floor();
		m_upper = upperBound.ceil();
	}

	/**
	 * [bound, bound]
	 * @param bound Rational for the lower and upper bound
	 */
	public Interval(Rational bound) {
		m_lower = bound.floor();
		m_upper = bound.ceil();
	}
	
	/**
	 * Creates an empty interval [1, -1]
	 */
	public Interval() {
		m_lower = Rational.ONE;
		m_upper = Rational.MONE;
	}
	
	/**
	 * @return A string representing the lower bound, null if at negative infinity
	 */
	public Rational getLowerBound() {
		return m_lower;
	}
	
	/**
	 * @return A string representing the upper bound, null if at positive infinity
	 */
	public Rational getUpperBound() {
		return m_upper;
	}

	/**
	 * @return True iff the interval is empty
	 */
	public boolean isEmpty() {
		return m_lower.compareTo(m_upper) > 0;
	}
	
	/**
	 * @return A copy of this interval in an independant object
	 */
	public Interval copy() {
		if (isEmpty()) return new Interval();
		
		return new Interval(m_lower, m_upper);
	}
	
	/**
	 * @param interval
	 * @return True if this interval and the given interval are equal
	 */
	public boolean isEqual(Interval interval) {
		if (isEmpty() && interval.isEmpty())
			return true;
		
		boolean lowerEqual = m_lower.compareTo(interval.getLowerBound()) == 0;
			
		boolean upperEqual = m_upper.compareTo(interval.getUpperBound()) == 0;
		
		return lowerEqual && upperEqual;
	}
	
	/**
	 * @return True iff the interval is an interval [a, a] containing only a single integer value
	 */
	public boolean isSingleValueInterval() {
		return m_lower.compareTo(m_upper) == 0;
	}
	
	public String toString() {
		if (isEmpty()) return "{}";
		String lower = (m_lower.compareTo(Rational.NEGATIVE_INFINITY) == 0) ?  "(-infinity" : "[" + m_lower.toString();
		String upper = (m_upper.compareTo(Rational.POSITIVE_INFINITY) == 0) ?  "infinity)" : m_upper.toString() + "]";
		return lower + ", " + upper;
	}
}
