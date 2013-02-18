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

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;


/**
 *  Represents a formula that is a (non-trivial) disjunction of flat formulas. 
 */
class ClauseFormula extends FlatFormula implements ClauseDeletionHook {
	final FlatFormula[] subformulas;
	final NegClauseFormula negated;
	Term smtFormula;
	NamedAtom lit;
	boolean auxAxiomsAdded;
	
	public ClauseFormula(ConvertFormula converter, FlatFormula[] subformulas) {
		super(converter);
		negated = new NegClauseFormula(converter, this);
		this.subformulas = subformulas;
	}

	public FlatFormula negate() {
		return negated;
	}
	
	public void addAuxAxioms() {
		Literal[] lits = new Literal[subformulas.length+1];
		/* "lit ==> subformula"  is "!lit || subformula" */
		lits[0] = lit.negate();
		int i = 1;
		for (FlatFormula l : subformulas) {
			lits[i++] = l.getLiteral();
		}
		m_converter.addClause(lits, this, true);
		auxAxiomsAdded = true;
	}

	//@Override
	public void addAsAxiom(ClauseDeletionHook hook) {
		Literal[] lits = new Literal[subformulas.length];
		int i = 0;
		for (FlatFormula l: subformulas) {
			lits[i++] = l.getLiteral();
		}
		m_converter.addClause(lits, hook, false);
	}
	
	//@Override
	public Term getSMTTerm(boolean useAuxVars) {
		if (smtFormula == null) {
			Term[] subs = new Term[subformulas.length];
			int i = 0;
			for	(FlatFormula l: subformulas)
				subs[i++] = l.getSMTTerm(useAuxVars);
			smtFormula = m_converter.dpllEngine.getSMTTheory().or(subs);
		}
		return smtFormula;
	}

	//@Override
	public Literal getLiteral() {
		if (lit == null) {
			lit = m_converter.createAnonAtom(getSMTTerm());
			m_converter.m_RemoveLit.add(this);
		}
		if (!auxAxiomsAdded)
			addAuxAxioms();
		return lit;
	}

	//@Override
	public Collection<FlatFormula> getSubFormulas() {
		return Arrays.asList(subformulas);
	}
	
	//@Override
	public void toStringHelper(StringBuilder sb, HashSet<FlatTerm> visited) {
		sb.append("[").append(hashCode()).append("]");
		if (visited.contains(this))
			return;
		visited.add(this);
		sb.append("(OR");
		for (FlatFormula f : subformulas) {
			sb.append(" ");
			f.toStringHelper(sb, visited);
		}
		sb.append(")");
	}
	
	public void literalRemoved() {
		lit = null;
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
