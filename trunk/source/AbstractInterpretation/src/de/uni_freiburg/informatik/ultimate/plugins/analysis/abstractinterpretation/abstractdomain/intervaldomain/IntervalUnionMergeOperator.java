/*
 * Copyright (C) 2014-2015 Christopher Dillo
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
