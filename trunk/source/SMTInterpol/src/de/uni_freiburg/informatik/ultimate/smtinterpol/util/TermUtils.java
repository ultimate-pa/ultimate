/*
 * Copyright (C) 2024 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class TermUtils {

	/**
	 * Returns true iff term is an ApplicationTerm of the internal function
	 * symbol with the given name.
	 * @param funcName the name of the function symbol.
	 * @param term The term to test.
	 * @return true iff term is the right application term.
	 */
	public static boolean isApplication(String funcName, Term term) {
		if (!(term instanceof ApplicationTerm)) {
			return false;
		}
		final FunctionSymbol fsymb = ((ApplicationTerm) term).getFunction();
		// we can use == as all symbols are interned.
		return fsymb.isIntern() && fsymb.getName() == funcName;
	}
}
