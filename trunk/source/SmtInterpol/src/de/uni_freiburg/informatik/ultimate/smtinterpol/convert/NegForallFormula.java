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

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;


public class NegForallFormula extends FlatFormula implements ClauseDeletionHook {
	ForallFormula positive;
	boolean auxAxiomsAdded;
	
	public NegForallFormula(ForallFormula pos) {
		super(pos.m_converter);
		this.positive = pos;
	}

	public FlatFormula negate() {
		return positive;
	}
	
	public void addAuxAxioms() {
		// !lit => skolemization is lit || skolemization
		FlatFormula skolem = getSkolemSub();
		HashSet<Literal> lits = new HashSet<Literal>();
		lits.add(positive.lit);
		for (FlatFormula ff : skolem.getSubFormulas())
			lits.add(ff.getLiteral());
		m_converter.addClause(lits.toArray(new Literal[lits.size()]), this, false);
		auxAxiomsAdded = true;
	}
	
	@Override
	public void addAsAxiom(ClauseDeletionHook hook) {
		getSkolemSub().addAsAxiom(hook);
	}
	
	//@Override
	public Term getSMTTerm(boolean useAuxVars) {
		return m_converter.dpllEngine.getSMTTheory().not(positive.getSMTTerm(useAuxVars));
	}

	//@Override
	public Literal getLiteral() {
		if (positive.lit == null) {
			positive.lit = this.m_converter.createQuantifiedAtom(
					positive.getSMTTerm());
			m_converter.m_RemoveLit.add(positive);
		}
		if (!auxAxiomsAdded)
			addAuxAxioms();
		return positive.lit.negate();
	}

	public Set<FlatFormula> getSubFormulas() {
		return Collections.singleton((FlatFormula) this);
	}
	//@Override
	public void toStringHelper(StringBuilder sb, HashSet<FlatTerm> visited) {
		sb.append("(NOT ");
		positive.toStringHelper(sb, visited);
		sb.append(")");
	}
	Set<TermVariable> getFreeVars() {
		return positive.getFreeVars();
	}
	private FlatFormula getSkolemSub() {
//		// extracted from YieldTrigger::match
//		m_converter.letTable.beginScope();
//		try {
//			for (TermVariable tv : positive.vars)
//				m_converter.letTable.put(tv, m_converter.createSkolemConstantFor(tv));
//			return m_converter.convertFormula(positive.subformula);			
//		} finally {
//			m_converter.letTable.endScope();
//		}
		return null;
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
