/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;

public class TermTransferrerBooleanCore extends TermTransferrer {
	
	private final Term m_AuxiliaryTerm;
	private final String m_FreshTermPrefix = "FBV_";
	private int m_FreshTermCounter;
	private final ConstructionCache<Term, Term> m_ConstructionCache;

	public TermTransferrerBooleanCore(Script script) {
		super(script);
		m_AuxiliaryTerm = constructAuxiliaryTerm();
		m_FreshTermCounter = 0;
		IValueConstruction<Term, Term> valueComputation = new IValueConstruction<Term, Term>() {
			
			@Override
			public Term constructValue(Term key) {
				String name = m_FreshTermPrefix + m_FreshTermCounter;
				m_FreshTermCounter++;
				m_Script.declareFun(name, new Sort[0], m_Script.sort("Bool"));
				Term value = m_Script.term(name);
				m_BacktransferMapping.put(value, key);
				return value;
			}
		};
		m_ConstructionCache = new ConstructionCache<Term, Term>(valueComputation );
	}
	
	public Term constructAuxiliaryTerm() {
		String name = this.getClass().getCanonicalName() + "_AUX";
		m_Script.declareFun(name, new Sort[0], m_Script.sort("Bool"));
		return m_Script.term(name);
	}

	@Override
	protected void convert(Term term) {
		if (term.getSort().getName().equals("Bool")) {
			super.convert(term);
		} else {
			setResult(m_AuxiliaryTerm);
		}
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		
		if (Arrays.asList(newArgs).contains(m_AuxiliaryTerm)) {
			Term result = m_ConstructionCache.getOrConstuct(appTerm);
			setResult(result);
		} else {
			super.convertApplicationTerm(appTerm, newArgs);
		}
	}
	
	
	
	

}
