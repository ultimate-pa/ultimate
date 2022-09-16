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
package de.uni_freiburg.informatik.ultimate.smtinterpol.dpll;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;


public abstract class DPLLAtom extends Literal {

	public static class TrueAtom extends DPLLAtom {

		public TrueAtom() {
			super(0, 0);
			mDecideStatus = this;
			mDecideLevel = 0;
		}

		@Override
		public Term getSMTFormula(final Theory smtTheory) {
			return smtTheory.mTrue;
		}

	}

	public static class NegLiteral extends Literal {
		public NegLiteral(final DPLLAtom atom) {
			super(~atom.hashCode());//TODO is bit-flipping a good hash???
			mAtom = atom;
			mNegated = atom;
		}
		@Override
		public int getSign() {
			return -1;
		}
		@Override
		public String toString() {
			return mAtom.toStringNegated();
		}
		@Override
		public Term getSMTFormula(final Theory smtTheory) {
			return mAtom.getNegatedSMTFormula(smtTheory);
		}
	}

	int mDecideLevel = -1;
	int mStackPosition = -1;
	Literal mDecideStatus;
	Literal mLastStatus;
	double  mActivity;
	public Object  mExplanation;
	Clause.WatchList mBacktrackWatchers = new Clause.WatchList();
	int mAtomQueueIndex = -1;
	final int mAssertionstacklevel;
	boolean mPreferredStatusIsLocked;

	public DPLLAtom(final int hash, final int assertionstacklevel) {
		super(hash);
		mAtom = this;
		mNegated = new NegLiteral(this);
		mAssertionstacklevel = assertionstacklevel;
		mLastStatus = mNegated;
		mPreferredStatusIsLocked = false;
	}

	/**
	 * Compares two atoms with respect to their activity. Do not override!
	 */
	public final int compareActivityTo(final DPLLAtom other) {
		return mActivity < other.mActivity ? 1
				: mActivity == other.mActivity ? 0 : -1;
	}

	/**
	 * Returns 1, since an atom is always positive.
	 */
	@Override
	public int getSign() {
		return 1;
	}

	/**
	 * The decide level of the atom. This is the number of atoms that were decided before this atom got its truth value.
	 * It is -1 if the atom is currently unset.
	 *
	 * @return the decide level of the literal.
	 */
	public final int getDecideLevel() {
		return mDecideLevel;
	}

	/**
	 * The stack position. This is the position in the DPLL stack that contains the current atom (or negated atom). It
	 * is -1 if the atom is currently unset.
	 *
	 * @return the stack position.
	 */
	public final int getStackPosition() {
		return mStackPosition;
	}

	/**
	 * Returns a string representation of the negated atoms.
	 * Subclasses may overwrite this for pretty output.
	 */
	public String toStringNegated() {
		return "!(" + toString() + ")";
	}

	/**
	 * Returns a SMT formula representing the negated atoms.
	 * Subclasses may overwrite this for pretty output.
	 */
	public final Term getNegatedSMTFormula(final Theory smtTheory) {
		return smtTheory.not(getSMTFormula(smtTheory));
	}

	/**
	 * Returns the status of an atom:
	 * null if atom is undecided,
	 * atom if atom should be true,
	 * atom.negate() if atom should be false.
	 */
	public Literal getDecideStatus() {
		return mDecideStatus;
	}

	public int getAssertionStackLevel() {
		return mAssertionstacklevel;
	}

	public boolean preferredStatusIsLocked() {
		return mPreferredStatusIsLocked;
	}

	public void lockPreferredStatus() {
		mPreferredStatusIsLocked = true;
	}

	public void unlockPreferredStatus() {
		mPreferredStatusIsLocked = false;
	}

	public void setPreferredStatus(final Literal status) {
		if (mPreferredStatusIsLocked) {
			throw new SMTLIBException("PreferredStatus must not be changed, since it is locked!");
		}
		mLastStatus = status;
//		activity += 1.0;
	}

	public Literal getPreferredStatus() {
		return mLastStatus;
	}
}
