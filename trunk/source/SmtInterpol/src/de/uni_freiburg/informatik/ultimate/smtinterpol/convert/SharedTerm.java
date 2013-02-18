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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinVar;

public class SharedTerm {
	
	private final Clausifier m_Clausifier;
	private final Term m_Term;
	private final IAnnotation m_Annot;
	
	// fields for theory.cclosure (Congruence Closure)
	CCTerm m_ccterm;
	
	// fields for theory.linar (Linear Arithmetic)
	LinVar m_linvar;
	Rational m_factor, m_offset;
	
	private Term m_RealTerm = null;
	
	public SharedTerm(Clausifier clausifier, Term term) {
		m_Clausifier = clausifier;
		m_Term = term;
		if (clausifier.getEngine().isProofGenerationEnabled())
			m_Annot = m_Clausifier.getAnnotation();
		else
			m_Annot = null;
	}
	
	public void setLinVar(Rational factor, LinVar linvar, Rational offset) {
		m_factor = factor;
		m_linvar = linvar;
		m_offset = offset;
	}
	
	public void share() {
		if (m_Clausifier.getLogger().isInfoEnabled())
			m_Clausifier.getLogger().info("Sharing term: "+this);
		assert (m_ccterm != null && m_offset != null);
		m_Clausifier.getLASolver().share(this);
		m_ccterm.share(m_Clausifier.getCClosure(), this);
	}
		
	public void shareWithLinAr() {
		if (m_offset != null)
			return;
		assert getSort().isNumericSort() : "Sharing non-numeric sort?";
		
		if (m_Term instanceof SMTAffineTerm) {
			m_Clausifier.getLASolver().generateSharedVar(
					this, m_Clausifier.createMutableAffinTerm(
							(SMTAffineTerm) m_Term),
					m_Clausifier.getStackLevel());
		} else {
			boolean isint = getSort().getName().equals("Int");
			m_linvar = m_Clausifier.getLASolver().addVar(this, isint,
					m_Clausifier.getStackLevel());
			
			m_factor = Rational.ONE;
			m_offset = Rational.ZERO;
		}
		m_Clausifier.addUnshareLA(this);
		if (m_ccterm != null)
			share();
	}
	
	public EqualityProxy createEquality(SharedTerm other) {
		SharedTerm a = this, b = other;
		if (getSort() != other.getSort()) {
			// LIRA: convert both terms to reals.
			if (getSort().getName().equals("Real")) {
				b = m_Clausifier.toReal(b);
			} else {
				a = m_Clausifier.toReal(a);
			}
		}
		return m_Clausifier.createEqualityProxy(a, b);
	}

	public void unshareLA() {
		m_factor = null;
		m_linvar = null;
		m_offset = null;
	}
	
	public void unshareCC() {
		m_ccterm = null;
	}

	public LinVar getLinVar() {
		return m_linvar;
	}
	public Rational getOffset() {
		return m_offset;
	}
	public Rational getFactor() {
		return m_factor;
	}

	public boolean validShared() {
		return m_ccterm != null && m_offset != null;
	}
	
	public Sort getSort() {
		return m_Term.getSort();
	}

	public Term getTerm() {
		return m_Term;
	}
	/**
	 * Get a term that can be used outside of SMTInterpol.  The result is equal
	 * to {@link #getTerm()} unless this function returns a
	 * {@link SMTAffineTerm}.  In this case, the result equals the application
	 * of {@link SMTAffineTerm#cleanup(Term)} applied to {@link #getTerm()}.
	 * @return A cleaned up term.
	 */
	public Term getRealTerm() {
		if (m_RealTerm == null)
			m_RealTerm = SMTAffineTerm.cleanup(m_Term);
		return m_RealTerm;
	}
	
	public IAnnotation getAnnotation() {
		return m_Annot;
	}
	
	public Clausifier getClausifier() {
		return m_Clausifier;
	}

	public CCTerm getCCTerm() {
		return m_ccterm;
	}
	
	public int hashCode() {
		return m_Term.hashCode();
	}
	
	public String toString() {
		return SMTAffineTerm.cleanup(m_Term).toString();
	}
	
	void setCCTerm(CCTerm ccterm) {
		assert(m_ccterm == null);
		m_ccterm = ccterm;
		m_Clausifier.addUnshareCC(this);
		if (m_offset != null)
			share();
	}
}
