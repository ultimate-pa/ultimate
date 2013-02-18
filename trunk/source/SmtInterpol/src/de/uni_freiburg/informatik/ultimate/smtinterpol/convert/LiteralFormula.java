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
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

class LiteralFormula extends FlatFormula {
	class NegatedFormula extends FlatFormula {
		private NegatedFormula(ConvertFormula converter) {
			super(converter);
		}

		//@Override
		public Term getSMTTerm(boolean useAuxVars) {
			return m_converter.dpllEngine.getSMTTheory()
				.not(negate().getSMTTerm(useAuxVars));
		}

		//@Override
		public Literal getLiteral() {
			return negate().getLiteral().negate();
		}

		//@Override
		public void toStringHelper(StringBuilder sb, HashSet<FlatTerm> visited) {
			sb.append("!");
			LiteralFormula.this.toStringHelper(sb, visited);
		}

		//@Override
		public void addAsAxiom(ClauseDeletionHook hook) {
			m_converter.addClause(new Literal[] { getLiteral() }, hook, false);
		}

		public Set<FlatFormula> getSubFormulas() {
			return Collections.singleton((FlatFormula) this);
		}

		@Override
		public FlatFormula negate() {
			return LiteralFormula.this;
		}

		public void accept(FlatTermVisitor visitor) {
			visitor.visit(this);
		}
	}
	final Term m_SmtTerm;
	Literal lit;
	FlatFormula negated;
	
	public LiteralFormula(ConvertFormula converter, Term smtTerm) {
		super(converter);
		this.m_SmtTerm = smtTerm;
		negated = new NegatedFormula(converter);
	}
	
	public FlatFormula negate() {
		return negated;
	}
	//@Override
	public Term getSMTTerm(boolean useAuxVars) {
		return m_SmtTerm;
	}
	//@Override
	public Literal getLiteral() {
		if (lit == null) {
			lit = m_converter.createBooleanVar(m_SmtTerm);
			m_converter.m_RemoveLit.add(this);
		}
		return lit;
	}
	//@Override
	public void toStringHelper(StringBuilder sb, HashSet<FlatTerm> visited) {
		sb.append(m_SmtTerm);
	}

	//@Override
	public void addAsAxiom(ClauseDeletionHook hook) {
		m_converter.addClause(new Literal[] { getLiteral() }, hook, false);
	}

	public Set<FlatFormula> getSubFormulas() {
		return Collections.singleton((FlatFormula) this);
	}

	@Override
	public void literalRemoved() {
		lit = null;
	}

	public void accept(FlatTermVisitor visitor) {
		visitor.visit(this);
	}
}
