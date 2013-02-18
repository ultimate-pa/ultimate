/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Valuation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;

// For some strange reasons we have to support the interface to other solvers...

/**
 * An utility implementation of the {@link Valuation} interface.  This
 * implementation just wraps a map containing the answer to a
 * <code>get-value</code> call.
 * @author Juergen Christ
 */
public class MapValuation implements Valuation {

	/**
	 * The backing map.
	 */
	private Map<Term, Term> m_Values;
	
	/**
	 * Create a new map valuation.
	 * @param values The backing map.
	 */
	public MapValuation(Map<Term, Term> values) {
		m_Values = values;
	}
	
	@Override
	public Term get(Term t) {
		return m_Values.get(t);
	}
	
	public String toString() {
		PrintTerm pt = new PrintTerm();
		StringBuilder sb = new StringBuilder();
		sb.append('(');
		String sep = "";
		String itemSep = Config.RESULTS_ONE_PER_LINE ? 
				System.getProperty("line.separator") + " " : " "; 
		for (Map.Entry<Term, Term> me : m_Values.entrySet()) {
			sb.append(sep);
			sb.append('(');
			pt.append(sb, me.getKey());
			sb.append(' ');
			pt.append(sb, me.getValue());
			sb.append(')');
			sep = itemSep;
		}
		sb.append(')');
		return sb.toString();
	}

}
