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

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;

public class NamedAtom extends DPLLAtom {
	public final static Annotation[] QUOTED = new Annotation[] {
		new Annotation(":quoted", null)
	};
	private final Term mSmtAtom;
	
	public NamedAtom(Term smtAtom, int assertionstacklevel) {
		super(smtAtom.hashCode(), assertionstacklevel);
		assert Config.EXPENSIVE_ASSERTS ? smtAtom == SMTAffineTerm.cleanup(smtAtom) : true;
		mSmtAtom = smtAtom;
	}
	
	@Override
	public String toString() {
		return mSmtAtom.toString();
	}

	@Override
	public Term getSMTFormula(Theory smtTheory, boolean quoted) {
		return quoted ? smtTheory.annotatedTerm(QUOTED, mSmtAtom) : mSmtAtom;
	}
	
	public int containsTerm(TermVariable tv) {
		return 0;
	}
	
	@Override
	public boolean equals(Object other) { // NOCHECKSTYLE see Literal.hashCode()
		return other instanceof NamedAtom
			&& ((NamedAtom) other).mSmtAtom == mSmtAtom;
	}
}
