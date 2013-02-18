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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleListable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAEquality;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class CCEquality extends DPLLAtom {
	private CCTerm m_lhs, m_rhs;
	CCEquality m_diseqReason;
	private LAEquality m_lasd;
	private Rational m_LAFactor;
	private Entry m_entry;
	int stackDepth = -1;
	
	class Entry extends SimpleListable<Entry> {
		public CCEquality getCCEquality() {
			return CCEquality.this;
		}
	}
	
	CCEquality(int assertionstacklevel, CCTerm c1, CCTerm c2) {
		super(HashUtils.hashJenkins(c1.hashCode(), c2), assertionstacklevel);
		this.m_lhs = c1;
		this.m_rhs = c2;
		this.m_entry = new Entry();
	}	
	
	public CCTerm getLhs() {
		return m_lhs;
	}

	public CCTerm getRhs() {
		return m_rhs;
	}
	
	public Entry getEntry() {
		return m_entry;
	}
	
	public LAEquality getLASharedData() {
		return m_lasd;
	}
	
	public void setLASharedData(LAEquality lasd, Rational factor) {
		m_lasd = lasd;
		m_LAFactor = factor;
	}
	
	/**
	 * Returns the linar factor. This is the factor f, such that 
	 * <code>f * (getLhs() - getRhs()) == getLASharedData().getVar()</code>
	 * @return the factor.
	 */
	public Rational getLAFactor() {
		return m_LAFactor;
	}

	public void removeLASharedData() {
		m_lasd = null;
		m_LAFactor = null;
	}
	
	public Term getSMTFormula(Theory smtTheory, boolean quoted) {
		Term lhs = m_lhs.toSMTTerm(smtTheory, quoted);
		Term rhs = m_rhs.toSMTTerm(smtTheory, quoted);
		return smtTheory.term("=", lhs, rhs);
	}

	public String toString() {
		return m_lhs + " == " + m_rhs;
	}
}
