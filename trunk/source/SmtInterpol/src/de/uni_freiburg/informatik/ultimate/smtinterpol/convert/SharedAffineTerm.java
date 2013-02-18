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

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;


public class SharedAffineTerm extends SharedTermOld {
	public SharedAffineTerm(ConvertFormula converter, AffineTerm at) {
		super(converter);
		this.m_affineTerm = at;
	}

	AffineTerm m_affineTerm;
	
	@Override
	public SharedAffineTerm toShared() {
		return this;
	}

	public CCTerm toCCTerm() {
		if (m_ccterm == null) {
//			m_ccterm = m_converter.cclosure.createAnonTerm(this);
			share();
			m_converter.m_UnshareCC.add(this);
		}
		return m_ccterm;
	}
	
	@Override
	public AffineTerm toAffineTerm() {
		return m_affineTerm;
	}

	@Override
	public void shareWithLinAr() {
		if (m_offset == null) {
//			m_converter.linarSolver.generateSharedVar
//				(this, m_affineTerm.getMutableAffinTerm(), m_converter.m_stackLevel);
		}
	}
	
	@Override
	public Term getSMTTerm(boolean useAuxVars) {
		return m_affineTerm.getSMTTerm(useAuxVars);
	}

	@Override
	public Sort getSort() {
		return m_affineTerm.getSort();
	}

	@Override
	public void toStringHelper(StringBuilder sb, HashSet<FlatTerm> visited) {
		m_affineTerm.toStringHelper(sb, visited);
	}

	public void accept(FlatTermVisitor visitor) {
		visitor.visit(this);
	}
}
