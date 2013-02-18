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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinVar;

public abstract class SharedTermOld extends FlatTerm {
	public SharedTermOld(ConvertFormula converter) {
		super(converter);
		m_stackLevel = -1;
	}

	// fields for theory.cclosure (Congruence Closure)
	CCTerm m_ccterm;
	
	// fields for theory.linar (Linear Arithmetic)
	LinVar m_linvar;
	Rational m_factor, m_offset;
	
	// the stack level when this term became shared.
	int m_stackLevel;
	
	// end of theory specific fields.
	
	@Override
	public SharedTermOld toShared() {
		return this;
	}

	public void setLinVar(Rational factor, LinVar linvar, Rational offset) {
		m_factor = factor;
		m_linvar = linvar;
		m_offset = offset;
		m_converter.m_UnshareLA.add(this);
	}
	
	public void share() {
		if (m_converter.getLogger().isInfoEnabled())
			m_converter.getLogger().info("Sharing term: "+this);
		assert (m_ccterm != null && m_offset != null);
		m_stackLevel = m_converter.m_stackLevel;
//		m_converter.linarSolver.share(this);
//		m_ccterm.share(m_converter.cclosure, this);
	}
		
	public void shareWithLinAr() {
		if (m_offset != null)
			return;
		assert getSort().getName().equals("Int") 
			|| getSort().getName().equals("Real") : "Sharing non-numeric sort?";
		
		boolean isint = getSort().getName().equals("Int");
//		m_linvar = m_converter.linarSolver.addVar(this, isint, m_converter.m_stackLevel);
		
		m_factor = Rational.ONE;
		m_offset = Rational.ZERO;
		m_converter.m_UnshareLA.add(this);
		if (m_ccterm != null)
			share();
	}
	
	public FlatFormula createEquality(SharedTermOld other) {
		FlatTerm a = this, b = other;
		if (a.getSort() != b.getSort()) {
			// LIRA: convert both terms to reals.
			if (a.getSort().getName().equals("Real")) {
				b = new AffineTerm(b.toAffineTerm(), a.getSort());
			} else {
				a = new AffineTerm(a.toAffineTerm(), b.getSort());
			}
		}
		return m_converter.createEqualityFormula(a, b);
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
}
