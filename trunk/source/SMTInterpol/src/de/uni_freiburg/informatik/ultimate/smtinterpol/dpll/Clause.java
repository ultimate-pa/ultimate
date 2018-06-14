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

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode;

/**
 * This class represents a clause.  It basically consists of an array
 * of literals.  There is also some additional informations like activity,
 * literal watchers, proof information and stacklevel for push/pop mechanism.
 * 
 * @author Jochen Hoenicke
 * 
 */
public class Clause extends SimpleListable<Clause> {
	Literal[] mLiterals;
	
	/**
	 * The next watched clause on the watcher list.
	 * Each clause has two watchers.  The first watching lit 0, the next lit1.
	 * Their watchers form a linked list.  For memory efficiency reasons there 
	 * is no real data structure for watchers, but a clause and a bit is used
	 * to represent a watcher.
	 */
	Clause  mNextFirstWatch, mNextSecondWatch;
	/**
	 * A bitset telling if the next watcher for nextFirstWatch/nextSecondWatch
	 * is the first or second watcher in that clause.  Bit0 is 1, iff  the
	 * next watcher on the first list, which watches nextFirstWatch, is the
	 * second watcher of that clause.  Likewise Bit1 is 1, iff the next watcher
	 * on the second list is the second watcher of the clause nextSecondWatch.
	 */
	int     mNextIsSecond;
	/**
	 * A WatchList is a list of watchers.
	 * Each clause has two watchers.  The first watching lit 0, the next lit1.
	 * Their watchers form a linked list.  For memory efficiency reasons there 
	 * is no real data structure for watchers, but a clause and a bit is used
	 * to represent a watcher.
	 */
	final static class WatchList {
		Clause mHead;
		int    mHeadIndex;
		Clause mTail;
		int    mTailIndex;
		int    mSize;
		
		public WatchList() {
			mHead = mTail = null;
		}
		
		public boolean isEmpty() {
			return mHead == null;
		}
		
		public int size() {
			return mSize;
		}

		public void prepend(Clause c, int index) {
			if (mHead == null) {
				mTail = c;
				mTailIndex = index;
			} else {
				if (index == 0) {
					assert c.mNextFirstWatch == null;
					c.mNextFirstWatch = mHead;
					c.mNextIsSecond |= mHeadIndex;
				} else {
					assert c.mNextSecondWatch == null;
					c.mNextSecondWatch = mHead;
					c.mNextIsSecond |= mHeadIndex << 1;
				}
			}
			mHead = c;
			mHeadIndex = index;
			mSize++;
		}

		public void append(Clause c, int index) {
			if (mHead == null) {
				mHead = c;
				mHeadIndex = index;
			} else {
				final Clause t = mTail;
				if (mTailIndex == 0) {
					assert t.mNextFirstWatch == null;
					t.mNextFirstWatch = c;
					t.mNextIsSecond |= index;
				} else {
					assert t.mNextSecondWatch == null;
					t.mNextSecondWatch = c;
					t.mNextIsSecond |= index << 1;
				}
			}
			mTail = c;
			mTailIndex = index;
			mSize++;
		}

		public int getIndex() {
			return mHeadIndex;
		}

		public Clause removeFirst() {
			final Clause c = mHead;
			if (mHeadIndex == 0) {
				mHead = c.mNextFirstWatch;
				mHeadIndex = c.mNextIsSecond & 1;
				c.mNextFirstWatch = null;
				c.mNextIsSecond &= 2;
			} else {
				mHead = c.mNextSecondWatch;
				mHeadIndex = (c.mNextIsSecond & 2) >> 1;
				c.mNextSecondWatch = null;
				c.mNextIsSecond &= 1;
			}
			if (mHead == null) {
				mTail = null;
				mTailIndex = 0;
			}
			mSize--;
			return c;
		}

		public void moveAll(WatchList src) {
			if (src.mHead == null) {
				return;
			}

			append(src.mHead, src.mHeadIndex);
			mSize += src.mSize - 1;
			mTail = src.mTail;
			mTailIndex = src.mTailIndex;
			src.mHead = null;
			src.mHeadIndex = 0;
			src.mTail = null;
			src.mTailIndex = 0;
			src.mSize = 0;
		}
	}

	/**
	 * The activity of a clause. Infinity for clauses that are not inferred. If
	 * the activity drops below some point the clause is removed.
	 */
	double mActivity;
	/**
	 * The stacklevel this clause was introduced.
	 */
	final int mStacklevel;

	/**
	 * Proof annotation
	 */
	ProofNode mProof;

	ClauseDeletionHook mCleanupHook;
	
	public int getSize() {
		return mLiterals.length;
	}

	public Literal getLiteral(int i) {
		return mLiterals[i];
	}

	public Clause(Literal[] literals) {
		mLiterals = literals;
		mStacklevel = computeStackLevel();
	}

	public Clause(Literal[] literals, ProofNode proof) {
		mLiterals = literals;
		mProof = proof;
		mStacklevel = computeStackLevel();
	}

	public Clause(Literal[] literals, int stacklevel) {
		mLiterals = literals;
		mStacklevel = Math.max(stacklevel, computeStackLevel());
	}

	public Clause(Literal[] literals, ResolutionNode proof, int stacklevel) {
		mLiterals = literals;
		mProof = proof;
		mStacklevel = Math.max(stacklevel, computeStackLevel());
	}

	private final int computeStackLevel() {
		int sl = 0;
		for (final Literal lit : mLiterals) {
			if (lit.getAtom().mAssertionstacklevel > sl) {
				sl = lit.getAtom().mAssertionstacklevel;
			}
		}
		return sl;
	}

	@Override
	public String toString() {
		return Arrays.toString(mLiterals);
	}
	
	public String toSMTLIB(Theory smtTheory) {
		if (mLiterals.length == 0) {
			return "false";
		}
		if (mLiterals.length == 1) {
			return mLiterals[0].getSMTFormula(smtTheory, true).toString();
		}
		final StringBuilder sb = new StringBuilder("(or");
		for (final Literal l : mLiterals) {
			sb.append(' ').append(l.getSMTFormula(smtTheory, true));
		}
		sb.append(')');
		return sb.toString();
	}

	public void setActivityInfinite() {
		mActivity = Double.POSITIVE_INFINITY;
	}

	public void setProof(ProofNode proof) {
		mProof = proof;
	}

	public ProofNode getProof() {
		return mProof;
	}

	public void setDeletionHook(ClauseDeletionHook hook) {
		mCleanupHook = hook;
	}

	public boolean doCleanup(DPLLEngine engine) {
		return mCleanupHook == null
		        ? true : mCleanupHook.clauseDeleted(this, engine);
	}

	/**
	 * Returns true, if the clause contains the literal with the same polarity.
	 * @param lit the literal it should contain.
	 * @return true, if the clause contains the literal with the same polarity.
	 */
	public boolean contains(Literal lit) {
		for (final Literal l : mLiterals) {
			if (l == lit) {
				return true;
			}
		}
		return false;
	}
	
	public Term toTerm(Theory theory) {
		if (mLiterals.length == 0) {
			return theory.mFalse;
		}
		if (mLiterals.length == 1) {
			return mLiterals[0].getSMTFormula(theory, true);
		}
		final Term[] args = new Term[mLiterals.length];
		for (int i = 0; i < mLiterals.length; ++i) {
			args[i] = mLiterals[i].getSMTFormula(theory, true);
		}
		return theory.term("or", args);
	}
	
}
