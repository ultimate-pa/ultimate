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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.topbottomdomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.topbottomdomain.TopBottomValue.TopBottom;

/**
 * @author Christopher Dillo
 *
 */
public class TopBottomMergeWideningOperator implements IWideningOperator<TopBottom>,
		IMergeOperator<TopBottom> {
	
	private TopBottomDomainFactory m_factory;
	
	private Logger m_logger;
	
	public TopBottomMergeWideningOperator(TopBottomDomainFactory factory, Logger logger) {
		m_factory = factory;
		m_logger = logger;
	}

	public static String getName() {
		return "TOP-BOTTOM Merge & Widening";
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator#apply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue, de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public TopBottomValue apply(IAbstractValue<?> oldValue, IAbstractValue<?> newValue) {
		TopBottomValue bvalA = (TopBottomValue) oldValue;
		TopBottomValue bvalB = (TopBottomValue) newValue; 
		
		// invalid state objects
		if ((bvalA == null) || (bvalB == null)) {
			return m_factory.makeTopValue();
		}
		
		TopBottom bvA = bvalA.getValue();
		TopBottom bvB = bvalB.getValue();
		
		if (bvA == bvB) return m_factory.makeValue(bvA);

		if ((bvA == TopBottom.TOP) || (bvB == TopBottom.TOP))
			return m_factory.makeTopValue();

		return m_factory.makeBottomValue();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator#copy()
	 */
	@Override
	public TopBottomMergeWideningOperator copy() {
		return new TopBottomMergeWideningOperator(m_factory, m_logger);
	}

}
