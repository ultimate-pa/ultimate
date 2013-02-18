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

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;


public class LeqZeroFormula extends FlatFormula {
	class NegatedFormula extends FlatFormula {
		public NegatedFormula() {
			super(LeqZeroFormula.this.m_converter);
		}
		
		public FlatFormula negate() {
			return LeqZeroFormula.this;
		}

		//@Override
		public Term getSMTTerm(boolean useAuxVars) {
			Theory t = m_converter.getTheory();
			Sort sort = mTerm.getSort();
			FunctionSymbol leq = t.getFunction(">", new Sort[] { sort, sort });
			return t.term(leq, 
					mTerm.getSMTTerm(useAuxVars), mTerm.convertConstant(Rational.ZERO)); 
		}

		//@Override
		public Literal getLiteral() {
			return negate().getLiteral().negate();
		}
		
		//@Override
		public void toStringHelper(StringBuilder sb, HashSet<FlatTerm> visited) {
			sb.append("(");
			mTerm.toStringHelper(sb, visited);
			sb.append(" > 0)");
		}

		//@Override
		public void addAsAxiom(ClauseDeletionHook hook) {
			m_converter.addClause(new Literal[] { getLiteral() });
		}

		public Set<FlatFormula> getSubFormulas() {
			return Collections.singleton((FlatFormula) this);
		}

		public void accept(FlatTermVisitor visitor) {
			visitor.visit(this);
		}
	}

	NegatedFormula negated;
	AffineTerm mTerm;
	Literal lit;

	public LeqZeroFormula(ConvertFormula converter, AffineTerm term) {
		super(converter);
		mTerm = term;
	}

	public FlatFormula negate() {
		if (negated == null) {
			negated = new NegatedFormula();
		}
		return negated;
	}

	//@Override
	public Term getSMTTerm(boolean useAuxVars) {
		Theory t = m_converter.getTheory();
		Sort sort = mTerm.getSort();
		FunctionSymbol leq = t.getFunction("<=", new Sort[] { sort, sort });
		return t.term(leq, 
				mTerm.getSMTTerm(useAuxVars), mTerm.convertConstant(Rational.ZERO)); 
	}
	
	//@Override
	public Literal getLiteral() {
		if (lit == null) {
			lit = m_converter.linarSolver.generateConstraint
				(mTerm.getMutableAffinTerm(), false, m_converter.m_stackLevel);
			m_converter.m_RemoveLit.add(this);
		}
		return lit;
	}

	//@Override
	public void toStringHelper(StringBuilder sb, HashSet<FlatTerm> visited) {
		sb.append("(");
		mTerm.toStringHelper(sb, visited);
		sb.append(" <= 0)");
	}

	//@Override
	public void addAsAxiom(ClauseDeletionHook hook) {
		m_converter.addClause(new Literal[] { getLiteral() }, hook, false);
	}

	public Set<FlatFormula> getSubFormulas() {
		return Collections.singleton((FlatFormula) this);
	}
	
	public void literalRemoved() {
		lit = null;
	}

	@Override
	public void accept(FlatTermVisitor visitor) {
		visitor.visit(this);
	}
}
