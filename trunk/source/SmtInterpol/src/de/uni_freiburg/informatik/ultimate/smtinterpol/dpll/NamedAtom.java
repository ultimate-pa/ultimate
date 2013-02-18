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
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;

public class NamedAtom extends DPLLAtom {
	public final static Annotation[] g_quoted = new Annotation[] {
		new Annotation(":quoted", null)
	};
	final Term smtAtom;
	
	public NamedAtom(Term smtAtom, int assertionstacklevel) {
		super(smtAtom.hashCode(), assertionstacklevel);
		this.smtAtom = SMTAffineTerm.cleanup(smtAtom);
	}
	
	public String toString() {
		return smtAtom.toString();
	}

	public Term getSMTFormula(Theory smtTheory, boolean quoted) {
		return quoted ? smtTheory.annotatedTerm(g_quoted, smtAtom) : smtAtom; 
	}
	
	public int containsTerm(TermVariable tv) {
		return 0;
	}
	
	public boolean equals(Object other) {
		return other instanceof NamedAtom &&
			((NamedAtom) other).smtAtom == smtAtom;
	}
}
