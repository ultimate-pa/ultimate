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
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;


class NegClauseFormula extends FlatFormula implements ClauseDeletionHook {
	/**
	 * 
	 */
	ClauseFormula positive;
	Term smtFormula;
	boolean auxAxiomsAdded;

	NegClauseFormula(ConvertFormula convertFormula, ClauseFormula pos) {
		super(convertFormula);
		this.positive = pos;
	}
	public FlatFormula negate() {
		return positive;
	}
	
	public void addAuxAxioms() {
		HashSet<FlatFormula> clause = new HashSet<FlatFormula>();
		/* "!lit ==> !subformula"  is "(!sf1 || lit) && ... && (!sfn || lit)" */
		for (FlatFormula l: positive.subformulas) {
			clause.addAll(l.negate().getSubFormulas());
			Literal[] lits = new Literal[clause.size()+1];
			int dest = 0;
			lits[dest++] = positive.lit;
			for (FlatFormula ff : clause) {
				lits[dest++] = ff.getLiteral();
			}
			m_converter.addClause(lits, this, true);
			clause.clear();
		}
		auxAxiomsAdded = true;
	}
	
	//@Override
	public void addAsAxiom(ClauseDeletionHook hook) {
		for (FlatFormula l: positive.subformulas) {
			l.negate().addAsAxiom(hook);
		}
	}
	
	//@Override
	public Term getSMTTerm(boolean useAuxVars) {
		if (smtFormula == null) {
			Term[] subs = new Term[positive.subformulas.length];
			int i = 0;
			for	(FlatFormula l: positive.subformulas)
				subs[i++] = l.negate().getSMTTerm(useAuxVars);
			smtFormula = m_converter.dpllEngine.getSMTTheory().and(subs);
		}
		return smtFormula;
	}

	//@Override
	public Literal getLiteral() {
		if (positive.lit == null) {
			positive.lit = this.m_converter.createAnonAtom(positive.getSMTTerm());
			m_converter.m_RemoveLit.add(positive);
		}
		if (!auxAxiomsAdded)
			addAuxAxioms();
		return positive.lit.negate();
	}

	public Set<FlatFormula> getSubFormulas() {
		return Collections.singleton((FlatFormula) this);
	}

	public void toStringHelper(StringBuilder sb, HashSet<FlatTerm> visited) {
		sb.append("(NOT ");
		positive.toStringHelper(sb, visited);
		sb.append(")");
	}
	
	@Override
	public boolean clauseDeleted(Clause c, DPLLEngine engine) {
		auxAxiomsAdded = false;
		return true;
	}

	public void accept(FlatTermVisitor visitor) {
		visitor.visit(this);
	}
}