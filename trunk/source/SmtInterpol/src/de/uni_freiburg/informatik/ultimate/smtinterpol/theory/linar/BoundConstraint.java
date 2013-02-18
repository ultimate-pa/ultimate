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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;


/**
 * Class representing an upper bound (var <= bound) on a variable.
 * 
 * @author Juergen Christ
 */
public class BoundConstraint extends DPLLAtom {
	final InfinitNumber m_bound;
	final InfinitNumber m_ibound;
	final LinVar m_var;

	public BoundConstraint(InfinitNumber bound, LinVar var, int assertionstacklevel) {
		super(HashUtils.hashJenkins(var.hashCode(), bound), assertionstacklevel);
		assert(bound.meps <= 0);
		assert(!var.misint || bound.isIntegral());
		m_bound = bound;
		m_ibound = bound.add(var.getEpsilon());
		assert(!m_bound.equals(m_ibound));
		m_var = var;
		assert !m_var.mconstraints.containsKey(bound);
		m_var.mconstraints.put(bound,this);
	}

	public LinVar getVar() {
		return m_var;
	}

	/**
	 * Return the bound if this atom should be true (var <= bound).
	 * 
	 * @return Bound set during construction
	 */
	public InfinitNumber getBound() {
		return m_bound;
	}
	
	/**
	 * Return the bound if this atom should be false (ibound <= var).
	 * 
	 * @return Bound converted to lower bound.
	 */
	public InfinitNumber getInverseBound() {
		return m_ibound;
	}

	@Override
	public String toStringNegated() {
		InfinitNumber ibound = getInverseBound();
		if (ibound.meps > 0)
			return "["+hashCode()+"]"+m_var + " > " + ibound.ma;
		else
			return "["+hashCode()+"]"+m_var + " >= " + ibound;
	}

	public String toString() {
		if (m_bound.meps < 0)
			return "["+hashCode()+"]"+m_var + " < " + m_bound.ma;
		else
			return "["+hashCode()+"]"+m_var + " <= " + m_bound;
	}

	// / --- Implies checks ---
	/**
	 * Is this constraint implied by a given upper bound?
	 * 
	 * This function returns <code>true</code> iff this bound is bigger than
	 * the given bound.
	 * 
	 * @param ubound
	 *            Upper bound currently set.
	 * @return true iff this bound is bigger than <code>ubound</code>.
	 */
	boolean impliedByUpperBound(InfinitNumber ubound) {
		return ubound.lesseq(m_bound);
	}

	/**
	 * Is this constraint implied by a given lower bound?
	 * 
	 * This function returns <code>true</code> iff this bound is smaller than
	 * the given bound.
	 * 
	 * @param lbound
	 *            Lower bound currently set.
	 * @return true iff this bound is smaller than <code>lbound</code>.
	 */
	boolean impliedByLowerBound(InfinitNumber lbound) {
		return getInverseBound().lesseq(lbound);
	}

	@Override
	public Term getSMTFormula(Theory smtTheory, boolean quoted) {
		MutableAffinTerm at = new MutableAffinTerm();
		at.add(Rational.ONE, m_var);
		at.add(m_bound.negate());
		return at.toSMTLibLeq0(smtTheory, quoted);
	}

	public boolean equals(Object other) {
		if (other instanceof BoundConstraint) {
			BoundConstraint o = (BoundConstraint) other;
			return o.m_var == m_var && o.m_bound.equals(m_bound);
		}
		return false;
	}
}
