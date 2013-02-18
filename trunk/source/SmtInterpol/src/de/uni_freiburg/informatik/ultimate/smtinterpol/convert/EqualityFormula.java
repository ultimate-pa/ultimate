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
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffinTerm;


public class EqualityFormula extends FlatFormula {
	class NegatedFormula extends FlatFormula {
		public NegatedFormula() {
			super(EqualityFormula.this.m_converter);
		}
		
		public FlatFormula negate() {
			return EqualityFormula.this;
		}

		//@Override
		public Term getSMTTerm(boolean useAuxVars) {
			Theory t = m_converter.getTheory();
			Sort sort = mLhs.getSort();
			FunctionSymbol neq = 
				t.getFunction("distinct", new Sort[] { sort, sort });
			return t.term(neq, mLhs.getSMTTerm(useAuxVars), mRhs.getSMTTerm(useAuxVars)); 
		}

		//@Override
		public Literal getLiteral() {
			return negate().getLiteral().negate();
		}
		
		//@Override
		public void toStringHelper(StringBuilder sb, HashSet<FlatTerm> visited) {
			sb.append("(");
			mLhs.toStringHelper(sb, visited);
			sb.append(" != ");
			mRhs.toStringHelper(sb, visited);
			sb.append(")");
		}

		//@Override
		public void addAsAxiom(ClauseDeletionHook hook) {
			m_converter.addClause(new Literal[] { getLiteral() }, hook, false);
		}

		public Set<FlatFormula> getSubFormulas() {
			return Collections.singleton((FlatFormula) this);
		}

		public void accept(FlatTermVisitor visitor) {
			visitor.visit(this);
		}
	}

	final SharedTermOld mLhs, mRhs;
	NegatedFormula negated;
	DPLLAtom m_eqAtom;
	
	public EqualityFormula(ConvertFormula converter, SharedTermOld lhs, SharedTermOld rhs) {
		super(converter);
		mLhs = lhs;
		mRhs = rhs;
	}

	public FlatFormula negate() {
		if (negated == null) {
			negated = new NegatedFormula();
		}
		return negated;
	}

	//@Override
	public void toStringHelper(StringBuilder sb, HashSet<FlatTerm> visited) {
		sb.append("(");
		mLhs.toStringHelper(sb, visited);
		sb.append(" == ");
		mRhs.toStringHelper(sb, visited);
		sb.append(")");
	}

	@Override
	public CCTerm toCCTerm() {
		if (m_ccterm == null && mRhs == m_converter.TRUE) {
			m_ccterm = mLhs.toCCTerm();
			FlatFormula eqFalse = 
				m_converter.createEqualityFormula(mLhs, m_converter.FALSE);
			FlatFormula excludedMiddle = 
				m_converter.convertDisjunction(this, eqFalse); 
			excludedMiddle.addAsAxiom(null);
			m_converter.m_UnshareCC.add(this);
			return m_ccterm;
		}
		return super.toCCTerm();
	}
	
	//@Override
	public Term getSMTTerm(boolean useAuxVars) {
		Theory t = m_converter.getTheory();
		Sort sort = mLhs.getSort();
		FunctionSymbol neq = 
			t.getFunction("=", new Sort[] { sort, sort });
		return t.term(neq, mLhs.getSMTTerm(useAuxVars), mRhs.getSMTTerm(useAuxVars)); 
	}
	
	public LAEquality createLAEquality() {
		/* create la part */
		MutableAffinTerm at = mLhs.toAffineTerm().getMutableAffinTerm();
		at.add(Rational.MONE, mRhs.toAffineTerm().getMutableAffinTerm());
		return mLhs.m_converter.linarSolver.createEquality
			(m_converter.m_stackLevel, at);
	}
	
	/**
	 * Creates a CCEquality for the given lhs and rhs.  The equality must
	 * match this EqualityFormula, i.e., 
	 * <code>lhs-rhs = c*(this.lhs-this.rhs)</code> for some rational c.
	 * This also has as side-effect, that it creates an LAEquality if it
	 * did not exists before.  For this reason it is only allowed to call
	 * it for integer or real terms. It will register LAEquality and CCEquality
	 * with each other.   
	 * @param lhs the left hand side.
	 * @param rhs the right hand side.
	 * @return The created (or cached) CCEquality.
	 */
	public CCEquality createCCEquality(SharedTermOld lhs, SharedTermOld rhs) {
		assert lhs.m_ccterm != null && rhs.m_ccterm != null;
		LAEquality laeq;
		if (m_eqAtom == null) {
			m_eqAtom = laeq = createLAEquality();
			m_converter.m_RemoveLit.add(this);
		} else if (m_eqAtom instanceof CCEquality) {
			CCEquality eq = (CCEquality) m_eqAtom;
			laeq = eq.getLASharedData();
			if (laeq == null) {
				MutableAffinTerm at = mLhs.toAffineTerm().getMutableAffinTerm();
				at.add(Rational.MONE, mRhs.toAffineTerm().getMutableAffinTerm());
				Rational normFactor = at.getGCD().inverse();
				laeq = createLAEquality();
				laeq.addDependentAtom(eq);
				eq.setLASharedData(laeq, normFactor);
			}
		} else {
			laeq = (LAEquality) m_eqAtom;
		}
		for (CCEquality eq : laeq.getDependentEqualities()) {
			assert (eq.getLASharedData() == laeq);
			if (eq.getLhs() == lhs.m_ccterm && eq.getRhs() == rhs.m_ccterm)
				return eq;
			if (eq.getRhs() == lhs.m_ccterm && eq.getLhs() == rhs.m_ccterm)
				return eq;
		}
		CCEquality eq = m_converter.cclosure.createCCEquality
			(m_converter.m_stackLevel, lhs.m_ccterm, rhs.m_ccterm);
		MutableAffinTerm at = lhs.toAffineTerm().getMutableAffinTerm();
		at.add(Rational.MONE, rhs.toAffineTerm().getMutableAffinTerm());
		Rational normFactor = at.getGCD().inverse();
		laeq.addDependentAtom(eq);
		eq.setLASharedData(laeq, normFactor);
		return eq;
	}

	private DPLLAtom createAtom() {
		
		if (mLhs.m_ccterm == null && mRhs.m_ccterm == null) {
			/* if both terms do not exist in CClosure yet, it may be better to
			 * create them in linear arithmetic.
			 * Do this, if we don't have a CClosure, or the other term is
			 * already in linear arithmetic.
			 */
			if (mLhs.m_converter.cclosure == null 
					|| mLhs.m_offset != null && mRhs.m_offset == null)
				mRhs.toAffineTerm().getMutableAffinTerm(); 
			if (mLhs.m_converter.cclosure == null 
					|| mLhs.m_offset == null && mRhs.m_offset != null)
				mLhs.toAffineTerm().getMutableAffinTerm(); 
		}
		
		/* check if the shared terms share at least one theory. */
		if (! ( (mLhs.m_ccterm != null && mRhs.m_ccterm != null)
				|| (mLhs.m_offset != null && mRhs.m_offset != null))) {
			/* let them share congruence closure */
			mLhs.toCCTerm();
			mRhs.toCCTerm();
		}

		/* Get linear arithmetic info, if both are arithmetic */
		if (mLhs.m_offset != null && mRhs.m_offset != null) {
			return createLAEquality();
		} else {
			/* create CC equality */
			return mLhs.m_converter.cclosure.createCCEquality
				(m_converter.m_stackLevel, mLhs.toCCTerm(), mRhs.toCCTerm());
		}		
	}
	
	//@Override
	public Literal getLiteral() {
		if (m_eqAtom == null) {
			m_eqAtom = createAtom();
			if (m_converter.dpllEngine.getLogger().isDebugEnabled())
				m_converter.dpllEngine.getLogger().debug("Created Equality: " + m_eqAtom);
			m_converter.m_RemoveLit.add(this);
		}
		return m_eqAtom;
	}

	//@Override
	public void addAsAxiom(ClauseDeletionHook hook) {
		m_converter.addClause(new Literal[] { getLiteral() });
	}
	
	public void literalRemoved() {
		m_eqAtom = null;
	}

	public Set<FlatFormula> getSubFormulas() {
		return Collections.singleton((FlatFormula) this);
	}

	public void accept(FlatTermVisitor visitor) {
		visitor.visit(this);
	}
}
