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

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;


class IfThenElseFormula extends FlatFormula implements ClauseDeletionHook {
	FlatFormula cond;
	FlatFormula thenForm;
	FlatFormula elseForm;
	IfThenElseFormula negated;
	Literal lit;
	boolean auxAxiomsAdded;
	HashSet<FlatFormula> subforms;
	Term smtFormula;
	
	public IfThenElseFormula(ConvertFormula converter, 
			FlatFormula cond, FlatFormula thenForm, FlatFormula elseForm) {
		super(converter);
		this.cond = cond;
		this.thenForm = thenForm;
		this.elseForm = elseForm;
		this.negated = new IfThenElseFormula(this);
	}
	/**
	 * Create a negated IfThenElse formula.
	 */
	private IfThenElseFormula(IfThenElseFormula negated) {
		super(negated.m_converter);
		this.cond = negated.cond;
		this.thenForm = negated.thenForm.negate();
		this.elseForm = negated.elseForm.negate();
		this.negated = negated;
	}

	public FlatFormula negate() {
		return negated;
	}
	
	//@Override
	public void addAuxAxioms() {
		Literal[] lits;
		int dest;
		/* "lit /\ cond ==> thenForm" and  "lit /\ !cond ==> elseForm" */
		HashSet<FlatFormula> clause = new HashSet<FlatFormula>();

		clause.addAll(cond.negate().getSubFormulas());
		clause.addAll(thenForm.getSubFormulas());
		lits = new Literal[clause.size()+1];
		dest = 0;
		lits[dest++] = lit.negate();
		for (FlatFormula ff : clause) {
			lits[dest++] = ff.getLiteral();
		}
		m_converter.addClause(lits, this, true);
		clause.clear();

		clause.addAll(cond.getSubFormulas());
		clause.addAll(elseForm.getSubFormulas());
		lits = new Literal[clause.size()+1];
		dest = 0;
		lits[dest++] = lit.negate();
		for (FlatFormula ff : clause) {
			lits[dest++] = ff.getLiteral();
		}
		m_converter.addClause(lits, this, true);
		auxAxiomsAdded = true;
	}

	//@Override
	public void addAsAxiom(ClauseDeletionHook hook) {
		Literal[] lits;
		int dest;
		/* "lit /\ cond ==> thenForm" and  "lit /\ !cond ==> elseForm" */
		HashSet<FlatFormula> clause = new HashSet<FlatFormula>();

		clause.addAll(cond.negate().getSubFormulas());
		clause.addAll(thenForm.getSubFormulas());
		lits = new Literal[clause.size()];
		dest = 0;
		for (FlatFormula ff : clause) {
			lits[dest++] = ff.getLiteral();
		}
		m_converter.addClause(lits, hook, false);
		clause.clear();

		clause.addAll(cond.getSubFormulas());
		clause.addAll(elseForm.getSubFormulas());
		lits = new Literal[clause.size()];
		dest = 0;
		for (FlatFormula ff : clause) {
			lits[dest++] = ff.getLiteral();
		}
		m_converter.addClause(lits, hook, false);
	}

	public Term getSMTTerm(boolean useAuxVars) {
		if (smtFormula == null) {
			if (thenForm == elseForm.negate())
				smtFormula = m_converter.dpllEngine.getSMTTheory().
					equals(cond.getSMTTerm(useAuxVars), 
							thenForm.getSMTTerm(useAuxVars));
			else
				smtFormula = m_converter.dpllEngine.getSMTTheory().
					ifthenelse(cond.getSMTTerm(useAuxVars), 
							thenForm.getSMTTerm(useAuxVars), 
							elseForm.getSMTTerm(useAuxVars));
		}
		return smtFormula;
	}

	//@Override
	public Literal getLiteral() {
		if (lit == null) {
			lit = m_converter.createAnonAtom(getSMTTerm());
			negated.lit = lit.negate();
			m_converter.m_RemoveLit.add(this);
		}
		if (!auxAxiomsAdded)
			addAuxAxioms();
		return lit;
	}

	public Set<FlatFormula> getSubFormulas() {
		if (subforms == null) {
			subforms = new HashSet<FlatFormula>();
			// (not (or (not cond) (not then))) 
			subforms.addAll(m_converter.convertDisjunction(cond.negate(),thenForm.negate()).negate().getSubFormulas());
			// (not (or cond (not else)))
			subforms.addAll(m_converter.convertDisjunction(cond,elseForm.negate()).negate().getSubFormulas());
		}
		return subforms;
	}
	
	public void toStringHelper(StringBuilder sb, HashSet<FlatTerm> visited) {
		sb.append("[").append(hashCode()).append("]");
		if (visited.contains(this))
			return;
		visited.add(this);
		sb.append("(IFTHENELSE");
		cond.toStringHelper(sb, visited);
		sb.append(" ");
		thenForm.toStringHelper(sb, visited);
		sb.append(" ");
		elseForm.toStringHelper(sb, visited);
		sb.append(")");
	}

	public void literalRemoved() {
		lit = null;
		negated.lit = null;
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
