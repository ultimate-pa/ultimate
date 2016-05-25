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
	final InfinitNumber mBound;
	final InfinitNumber mIBound;
	final LinVar mVar;

	public BoundConstraint(InfinitNumber bound, LinVar var, int assertionstacklevel) {
		super(HashUtils.hashJenkins(var.hashCode(), bound), assertionstacklevel);
		assert(bound.mEps <= 0);
		assert(!var.mIsInt || bound.isIntegral());
		mBound = bound;
		mIBound = bound.add(var.getEpsilon());
		assert(!mBound.equals(mIBound));
		mVar = var;
		assert !mVar.mConstraints.containsKey(bound);
		mVar.mConstraints.put(bound,this);
	}

	public LinVar getVar() {
		return mVar;
	}

	/**
	 * Return the bound if this atom should be true (var <= bound).
	 * 
	 * @return Bound set during construction
	 */
	public InfinitNumber getBound() {
		return mBound;
	}
	
	/**
	 * Return the bound if this atom should be false (ibound <= var).
	 * 
	 * @return Bound converted to lower bound.
	 */
	public InfinitNumber getInverseBound() {
		return mIBound;
	}

	@Override
	public String toStringNegated() {
		final InfinitNumber ibound = getInverseBound();
		if (ibound.mEps > 0) {
			return "[" + hashCode() + "]" + mVar + " > " + ibound.mA;
		} else {
			return "[" + hashCode() + "]" + mVar + " >= " + ibound;
		}
	}

	@Override
	public String toString() {
		if (mBound.mEps < 0) {
			return "[" + hashCode() + "]" + mVar + " < " + mBound.mA;
		} else {
			return "[" + hashCode() + "]" + mVar + " <= " + mBound;
		}
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
		return ubound.lesseq(mBound);
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
		final MutableAffinTerm at = new MutableAffinTerm();
		at.add(Rational.ONE, mVar);
		at.add(mBound.negate());
		return at.toSMTLibLeq0(smtTheory, quoted);
	}

	@Override
	public boolean equals(Object other) { //NOCHECKSTYLE
		if (other instanceof BoundConstraint) {
			final BoundConstraint o = (BoundConstraint) other;
			return o.mVar == mVar && o.mBound.equals(mBound);
		}
		return false;
	}
}
