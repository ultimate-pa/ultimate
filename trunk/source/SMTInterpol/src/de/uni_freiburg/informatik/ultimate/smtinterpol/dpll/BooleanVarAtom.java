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
package de.uni_freiburg.informatik.ultimate.smtinterpol.dpll;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class BooleanVarAtom extends DPLLAtom {
	final Term mVariable;

	public BooleanVarAtom(Term var, int assertionstacklevel) {
		super(var.hashCode(), assertionstacklevel);
		mVariable = var;
	}

	@Override
	public String toString() {
		return mVariable.toString();
	}

	@Override
	public Term getSMTFormula(Theory smtTheory, boolean quoted) {
		return mVariable;
	}

	@Override
	public boolean equals(Object other) { // NOCHECKSTYLE see Literal.hashCode()
		return other instanceof BooleanVarAtom
			&& ((BooleanVarAtom) other).mVariable == mVariable;
	}
}
