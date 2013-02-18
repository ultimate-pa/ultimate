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

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;

public abstract class FlatFormula extends SharedTermOld {
	public FlatFormula(ConvertFormula converter) {
		super(converter);
	}

	public final boolean isTrue() {
		return this == m_converter.TRUE;
	}

	public final boolean isFalse() {
		return this == m_converter.FALSE;
	}

	public abstract Literal getLiteral();
	public abstract FlatFormula negate();
	public abstract void addAsAxiom(ClauseDeletionHook hook);
	public abstract Collection<FlatFormula> getSubFormulas();
	public void literalRemoved() {
		// This formula should not be registered
		throw new AssertionError();
	}

	@Override
	public Sort getSort() {
		return m_converter.getTheory().getBooleanSort();
	}

	@Override
	public CCTerm toCCTerm() {
		if (m_ccterm == null) {
//			m_ccterm = m_converter.cclosure.createAnonTerm(this);
			if (this != m_converter.TRUE && this != m_converter.FALSE) {
				FlatFormula thenForm = m_converter.createEqualityFormula(this,
						m_converter.TRUE);
				FlatFormula elseForm = m_converter.createEqualityFormula(this,
						m_converter.FALSE);
				FlatFormula flatite = new IfThenElseFormula(m_converter, this,
						thenForm, elseForm);
				flatite.accept(m_converter.internalizer);
				flatite.addAsAxiom(null);
			}
			m_converter.m_UnshareCC.add(this);
		}
		return m_ccterm;
	}
}