/*
 * Copyright (C) 2012-2015 Evren Ermis
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

public class SubstituteTermTransformer extends TermTransformer{

//	private Term m_term = null;
//	private Term m_substitute = null;
	private HashMap<Term, Term> m_substitution = new HashMap<Term, Term>();
	
	public Term substitute(Term formula, Term term, Term substitute) {
//		m_term = term;
//		m_substitute = substitute;
		m_substitution.clear();
		m_substitution.put(term, substitute);
		Term result = transform(formula);
		return result;
	}
	
	public Term substitute(Term formula, HashMap<Term,Term> substitution) {
		m_substitution = substitution;
		Term result = transform(formula);
		return result;
	}
	
	protected void convert(Term term) {
		if (m_substitution.containsKey(term)) {
			super.setResult(m_substitution.get(term));
			return;
		}
		super.convert(term);
	}
	
}
