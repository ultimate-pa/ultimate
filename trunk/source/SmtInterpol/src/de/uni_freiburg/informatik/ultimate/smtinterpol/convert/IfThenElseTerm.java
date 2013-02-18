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
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;


public class IfThenElseTerm extends SharedTermOld implements ClauseDeletionHook {
	FlatFormula mCond;
	SharedTermOld mThen, mElse;
	private boolean axiomsCreated;
	private TermVariable m_auxVar;
		
	public IfThenElseTerm(ConvertFormula converter, 
			FlatFormula cond, SharedTermOld thenTerm, SharedTermOld elseTerm) {
		super(converter);
		assert (thenTerm.getSort() == elseTerm.getSort());
		mCond = cond;
		mThen = thenTerm;
		mElse = elseTerm;
	}

	public void createAxioms() {
		if (axiomsCreated)
			return;
		axiomsCreated = true;
		FlatFormula thenForm = 
			m_converter.createEqualityFormula(this, mThen);
		FlatFormula elseForm = 
			m_converter.createEqualityFormula(this, mElse);
		FlatFormula flatite = 
			new IfThenElseFormula(m_converter, mCond, thenForm, elseForm);
//		flatite.intern();
		flatite.accept(m_converter.internalizer);
		flatite.addAsAxiom(this);
	}
	
	public CCTerm toCCTerm() {
		if (m_ccterm == null) {
//			m_ccterm = m_converter.cclosure.createAnonTerm(this);
			if (m_offset != null)
				share();
//			createAxioms();
			m_converter.m_UnshareCC.add(this);
		}
		return m_ccterm;
	}
	
	public void shareWithLinAr() {
		super.shareWithLinAr();
//		createAxioms();
	}

	@Override
	public Term getSMTTerm(boolean useAuxVars) {
		if (useAuxVars) {
			if (m_auxVar == null)
				m_auxVar = m_converter.createAuxVariable(computeSMTTerm());
			return m_auxVar;
		}
		return computeSMTTerm();
	}

	public Term computeSMTTerm() {
		return m_converter.getTheory().ifthenelse
			(mCond.getSMTTerm(), mThen.getSMTTerm(), mElse.getSMTTerm());
	}

	@Override
	public Sort getSort() {
		return mThen.getSort();
	}

	public void toStringHelper(StringBuilder sb, HashSet<FlatTerm> visited) {
		sb.append("[").append(hashCode()).append("]");
		if (visited.contains(this))
			return;
		visited.add(this);
		sb.append("(");
		mCond.toStringHelper(sb, visited);
		sb.append(" ? ");
		mThen.toStringHelper(sb, visited);
		sb.append(" : ");
		mElse.toStringHelper(sb, visited);
		sb.append(")");
	}

	@Override
	public boolean clauseDeleted(Clause c, DPLLEngine engine) {
		axiomsCreated = false;
		return true;
	}

	public void accept(FlatTermVisitor visitor) {
		visitor.visit(this);
	}
}
