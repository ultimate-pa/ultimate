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

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
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
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeBoolValue(boolean)
	 */
	@Override
	public IntervalValue makeBoolValue(boolean bool) {
		return makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeBitVectorValue(java.lang.String)
	 */
	public IntervalValue makeBitVectorValue(String bitvector) {
		return makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeStringValue(java.lang.String)
	 */
	public IntervalValue makeStringValue(String value) {
		return makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#valueIsCompatible(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean valueBelongsToDomainSystem(IAbstractValue<?> value) {
		return (value instanceof IntervalValue);
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
