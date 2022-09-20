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

public class NamedAtom extends DPLLAtom {
	private final Term mSmtAtom;

	public NamedAtom(final Term smtAtom, final int assertionstacklevel) {
		super(smtAtom.hashCode(), assertionstacklevel);
		mSmtAtom = smtAtom;
	}

	@Override
	public String toString() {
		return mSmtAtom.toString();
	}

	@Override
	public Term getSMTFormula(final Theory smtTheory) {
		return mSmtAtom;
	}
}
