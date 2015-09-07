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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain.BoolValue.Bool;

/**
 * @author Christopher Dillo
 *
 */
public class BoolMergeWideningOperator implements IMergeOperator<Bool>,
		IWideningOperator<BoolValue.Bool> {
	
	private BoolDomainFactory m_factory;
	
	private Logger m_logger;
	
	public BoolMergeWideningOperator(BoolDomainFactory factory, Logger logger) {
		m_factory = factory;
		m_logger = logger;
	}

	public static String getName() {
		return "BOOL Merge & Widening";
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator#apply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue, de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue apply(IAbstractValue<?> valueA, IAbstractValue<?> valueB) {
		BoolValue bvalA = (BoolValue) valueA;
		BoolValue bvalB = (BoolValue) valueB; 
		
		// invalid state objects
		if ((bvalA == null) || (bvalB == null)) {
			return m_factory.makeTopValue();
		}
		
		Bool boolA = bvalA.getValue();
		Bool boolB = bvalB.getValue();
		
		if (boolA == boolB) return m_factory.makeValue(boolA);

		if (boolA == Bool.EMPTY) {
			if (boolB == Bool.TRUE) return m_factory.makeValue(Bool.TRUE);
			if (boolB == Bool.FALSE) return m_factory.makeValue(Bool.FALSE);
		}
		if (boolB == Bool.EMPTY) {
			if (boolA == Bool.TRUE) return m_factory.makeValue(Bool.TRUE);
			if (boolA == Bool.FALSE) return m_factory.makeValue(Bool.FALSE);
		}
		
		return m_factory.makeValue(Bool.UNKNOWN);
	}

	@Override
	public BoolMergeWideningOperator copy() {
		return new BoolMergeWideningOperator(m_factory, m_logger);
	}

}
