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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain.SignValue.Sign;

/**
 * @author Christopher Dillo
 *
 */
public class SignMergeWideningOperator implements IWideningOperator<Sign>, IMergeOperator<Sign> {
	
	private SignDomainFactory m_factory;
	
	private Logger m_logger;
	
	public SignMergeWideningOperator(SignDomainFactory factory, Logger logger) {
		m_factory = factory;
		m_logger = logger;
	}

	public static String getName() {
		return "SIGN Merge & Widening";
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator#apply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue, de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue apply(IAbstractValue<?> oldValue, IAbstractValue<?> newValue) {
		Sign oldV = (Sign) oldValue.getValue();
		Sign newV = (Sign) newValue.getValue();
		if ((oldV == null) || (newV == null)) return m_factory.makeTopValue();

		// old is PLUSMINUS : PLUSMINUS
		if (oldValue.isTop())
			return m_factory.makeValue(Sign.PLUSMINUS);
		
		// new is PLUSMINUS : PLUSMINUS
		if (newValue.isTop())
			return m_factory.makeValue(Sign.PLUSMINUS);
		
		// old is ZERO : new
		if (oldValue.isBottom())
			return m_factory.makeValue(newV);

		// new is ZERO : old
		if (newValue.isBottom())
			return m_factory.makeValue(oldV);
		
		// old is new : old (or new)
		if (oldV == newV)
			return m_factory.makeValue(oldV);
		
		// old is PLUS, new is MINUS or vice versa : PLUSMINUS
		return m_factory.makeValue(Sign.PLUSMINUS);
	}

	@Override
	public SignMergeWideningOperator copy() {
		return new SignMergeWideningOperator(m_factory, m_logger);
	}

}
