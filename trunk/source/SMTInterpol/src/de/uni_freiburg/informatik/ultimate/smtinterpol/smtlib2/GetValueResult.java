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
 * Class to represent a list of values. These are used for the get-value
 * response, which should print the values in SMT-LIB format.
 *
 * @author Jochen Hoenicke
 */
public class GetValueResult {
	private final Map<Term,Term> mValues;

	/**
	 * Create a get-value response.
	 *
	 * @param result a map from terms to their values (in the order they should be
	 *               output).
	 */
	public GetValueResult(Map<Term, Term> result) {
		mValues = result;
	}

	/**
	 * Convert S-expression to its string representation.
	 */
	@Override
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
		sb.append(')');
		return sb.toString();
	}
}
