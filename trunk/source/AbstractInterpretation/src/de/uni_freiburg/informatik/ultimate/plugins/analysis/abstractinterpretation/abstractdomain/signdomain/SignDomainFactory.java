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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain;

import java.math.BigDecimal;
import java.math.BigInteger;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain.SignValue.Sign;

/**
 * @author Christopher Dillo
 *
 */
public class SignDomainFactory implements IAbstractDomainFactory<Sign> {

	private static final String s_domainID = "SIGN";
	
	private final Logger m_logger;
	
	private final String m_wideningOperatorName, m_mergeOperatorName;

	public SignDomainFactory(Logger logger, String wideningOperatorName, String mergeOperatorName) {
		m_logger = logger;
		m_wideningOperatorName = wideningOperatorName;
		m_mergeOperatorName = mergeOperatorName;
	}
	
	public static String getDomainID() {
		return s_domainID;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeValue()
	 */
	@Override
	public SignValue makeValue(Sign value) {
		return new SignValue(value, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeTopValue()
	 */
	@Override
	public SignValue makeTopValue() {
		return new SignValue(Sign.PLUSMINUS, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeBottomValue()
	 */
	@Override
	public SignValue makeBottomValue() {
		return new SignValue(Sign.ZERO, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeIntegerValue(int)
	 */
	@Override
	public SignValue makeIntegerValue(String integer) {
		BigInteger number;
		try {
			number = new BigInteger(integer);
		} catch (NumberFormatException e) {
			m_logger.warn(String.format("Invalid number format: \"%s\" - Using Sign.PLUSMINUS", integer));
			return new SignValue(Sign.PLUSMINUS, this, m_logger);
		}
		
		int signum = number.signum();
		
		if (signum == 0)
			return new SignValue(Sign.ZERO, this, m_logger);
		
		if (signum < 0)
			return new SignValue(Sign.MINUS, this, m_logger);
		
		return new SignValue(Sign.PLUS, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeIntegerValue(int)
	 */
	@Override
	public SignValue makeRealValue(String real) {
		BigDecimal number;
		try {
			number = new BigDecimal(real);
		} catch (NumberFormatException e) {
			m_logger.warn(String.format("Invalid number format: \"%s\" - Using Sign.PLUSMINUS", real));
			return new SignValue(Sign.PLUSMINUS, this, m_logger);
		}
		
		int signum = number.signum();
		
		if (signum == 0)
			return new SignValue(Sign.ZERO, this, m_logger);
		
		if (signum < 0)
			return new SignValue(Sign.MINUS, this, m_logger);
		
		return new SignValue(Sign.PLUS, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeBoolValue(boolean)
	 */
	@Override
	public SignValue makeBoolValue(boolean bool) {
		return new SignValue(Sign.EMPTY, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeBitVectorValue(java.lang.String)
	 */
	public SignValue makeBitVectorValue(String bitvector) {
		return new SignValue(Sign.EMPTY, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeStringValue(java.lang.String)
	 */
	public SignValue makeStringValue(String value) {
		return new SignValue(Sign.EMPTY, this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#valueIsCompatible(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public boolean valueBelongsToDomainSystem(IAbstractValue<?> value) {
		return (value instanceof SignValue);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeWideningOperator()
	 */
	@Override
	public IWideningOperator<SignValue.Sign> getWideningOperator() {
		if (m_wideningOperatorName.equals(SignMergeWideningOperator.getName()))
			return new SignMergeWideningOperator(this, m_logger);
		
		// default: SignMergeWideningOperator
		m_logger.warn(String.format("Unknown Sign widening operator \"%s\" chosen, using \"%s\" instead",
				m_mergeOperatorName, SignMergeWideningOperator.getName()));
		return new SignMergeWideningOperator(this, m_logger);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeMergeOperator()
	 */
	@Override
	public IMergeOperator<SignValue.Sign> getMergeOperator() {
		if (m_mergeOperatorName.equals(SignMergeWideningOperator.getName()))
			return new SignMergeWideningOperator(this, m_logger);
		
		// default: SignMergeWideningOperator
		m_logger.warn(String.format("Unknown Sign merge operator \"%s\" chosen, using \"%s\" instead",
				m_mergeOperatorName, SignMergeWideningOperator.getName()));
		return new SignMergeWideningOperator(this, m_logger);
	}

}
