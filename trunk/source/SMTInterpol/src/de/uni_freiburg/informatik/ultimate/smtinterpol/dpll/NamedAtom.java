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
	public final static Annotation[] QUOTED = new Annotation[] {
		new Annotation(":quoted", null)
	};
	private final Term mSmtAtom;
//	private boolean mClean = false;
	
	public NamedAtom(Term smtAtom, int assertionstacklevel) {
		super(smtAtom.hashCode(), assertionstacklevel);
		this.mSmtAtom = smtAtom;//SMTAffineTerm.cleanup(smtAtom);
	}
	
	public String toString() {
//		if (!mClean)
//			cleanup();
		return SMTAffineTerm.cleanup(mSmtAtom).toString();
	}

	public Term getSMTFormula(Theory smtTheory, boolean quoted) {
//		if (!mClean)
//			cleanup();
		Term form = SMTAffineTerm.cleanup(mSmtAtom);
		return quoted ? smtTheory.annotatedTerm(QUOTED, form) : form;
	}
	
	public int containsTerm(TermVariable tv) {
		return 0;
	}
	
	public boolean equals(Object other) { // NOCHECKSTYLE see Literal.hashCode()
//		if (!mClean)
//			cleanup();
		return other instanceof NamedAtom
			&& ((NamedAtom) other).mSmtAtom == mSmtAtom;
	}
	
//	private void cleanup() {
//		mSmtAtom = SMTAffineTerm.cleanup(mSmtAtom);
//		mClean = true;
//	}
}
