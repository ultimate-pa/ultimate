/*
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;

/**
 * Class to represent a list of assertions.  These are used for the getAssertion response, which should
 * print the assertions as they were given (without let conversion).
 * 
 * @author hoenicke
 */
public class GetValueResult {
	private Map<Term,Term> mValues;

	public GetValueResult(Map<Term, Term> result) {
		this.mValues = result;
	}

	/**
	 * Convert S-expression to its string representation.
	 */
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		final PrintTerm pt = new PrintTerm();
		sb.append('(');
		String sep = "";
		final String itemSep = Config.RESULTS_ONE_PER_LINE ? System.getProperty("line.separator") + " " : " ";
		for (final Map.Entry<Term, Term> me : mValues.entrySet()) {
			sb.append(sep);
			sb.append('(');
			pt.append(sb, me.getKey());
			sb.append(' ');
			pt.append(sb, me.getValue());
			sb.append(')');
			sep = itemSep;
		}
		return sb.toString();
	}
}
