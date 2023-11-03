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
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofRules;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode;

/**
 * This class represents a clause. It basically consists of an array of
 * literals. There is also some additional informations like activity, literal
 * watchers, proof information and stacklevel for push/pop mechanism.
 *
 * @author Jochen Hoenicke
 *
 */
public class Clause extends SimpleListable<Clause> {
	Literal[] mLiterals;

	/**
	 * The next watched clause on the watcher list. Each clause has two watchers.
	 * The first watching lit 0, the next lit1. Their watchers form a linked list.
	 * For memory efficiency reasons there is no real data structure for watchers,
	 * but a clause and a bit is used to represent a watcher.
	 */
	Clause mNextFirstWatch, mNextSecondWatch;
	/**
	 * A bitset telling if the next watcher for nextFirstWatch/nextSecondWatch is
	 * the first or second watcher in that clause. Bit0 is 1, iff the next watcher
	 * on the first list, which watches nextFirstWatch, is the second watcher of
	 * that clause. Likewise Bit1 is 1, iff the next watcher on the second list is
	 * the second watcher of the clause nextSecondWatch.
	 */
	int mNextIsSecond;

	/**
	 * A WatchList is a list of watchers. Each clause with more than one literal has
	 * two watchers. The first watching lit 0, the next lit1. Their watchers form a
	 * linked list. A unit clause has only one watcher and the empty clause is
	 * immediately assigned to mUnsatClause to indicate a proof of unsatisfiable was
	 * found. For memory efficiency reasons there is no real data structure for
	 * watchers, but a clause and a bit is used to represent a watcher.
	 *
	 * A watcher is always on exactly one of the following three lists:
	 * <ul>
	 * <li>dpllEngine.mPendingWatcherList</li>
	 * <li>literal.mWatcher</li>
	 * <li>atom.mBacktrackWatcher</li>
	 * </ul>
	 *
	 * A watcher can only be on literal.mWatcher of its corresponding literal and
	 * only if it is not set to false. The watcher of a unit literal must not be on
	 * literal.mWatcher, because it needs to be propagated immediately. A watcher
	 * can only be on atom.mBacktrackWatcher of a literal in the same clause that is
	 * currently true. This can either be the watched literal or a different one
	 * (usually the other watched literal). A watcher can only be on
	 * mWatcherSetList, if its corresponding literal is currently false. In all
	 * other cases it is on the mPendingWatcherList where it is reassigned to a
	 * different list in dpllEngine.propagateClauses() when a literal is propagated
	 * or a better list is found for this watcher.
	 */
	final static class WatchList {
		Clause mHead;
		int mHeadIndex;
		Clause mTail;
		int mTailIndex;
		int mSize;

		public WatchList() {
			mHead = mTail = null;
		}

		public boolean isEmpty() {
			return mHead == null;
		}

		public int size() {
			return mSize;
		}

		public void prepend(final Clause c, final int index) {
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

		public void append(final Clause c, final int index) {
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

		public void moveAll(final WatchList src) {
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
	 * The activity of a clause. Infinity for clauses that are not inferred. If the
	 * activity drops below some point the clause is removed.
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

	public Literal getLiteral(final int i) {
		return mLiterals[i];
	}

	public Clause(final Literal[] literals) {
		mLiterals = literals;
		mStacklevel = computeStackLevel();
	}

	public Clause(final Literal[] literals, final ProofNode proof) {
		mLiterals = literals;
		mProof = proof;
		mStacklevel = computeStackLevel();
	}

	public Clause(final Literal[] literals, final int stacklevel) {
		mLiterals = literals;
		mStacklevel = Math.max(stacklevel, computeStackLevel());
	}

	public Clause(final Literal[] literals, final ResolutionNode proof, final int stacklevel) {
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

	public void setActivityInfinite() {
		mActivity = Double.POSITIVE_INFINITY;
	}

	public void setProof(final ProofNode proof) {
		mProof = proof;
	}

	public ProofNode getProof() {
		return mProof;
	}

	public void setDeletionHook(final ClauseDeletionHook hook) {
		mCleanupHook = hook;
	}

	public boolean doCleanup(final DPLLEngine engine) {
		return mCleanupHook == null ? true : mCleanupHook.clauseDeleted(this, engine);
	}

	/**
	 * Returns true, if the clause contains the literal with the same polarity.
	 * 
	 * @param lit
	 *            the literal it should contain.
	 * @return true, if the clause contains the literal with the same polarity.
	 */
	public boolean contains(final Literal lit) {
		for (final Literal l : mLiterals) {
			if (l == lit) {
				return true;
			}
		}
		return false;
	}

	public Term toTerm(final Theory theory) {
		if (mLiterals.length == 0) {
			return theory.mFalse;
		}
		if (mLiterals.length == 1) {
			return mLiterals[0].getSMTFormula(theory);
		}
		final Term[] args = new Term[mLiterals.length];
		for (int i = 0; i < mLiterals.length; ++i) {
			args[i] = mLiterals[i].getSMTFormula(theory);
		}
		return theory.term("or", args);
	}

	public Term[] toTermArray(final Theory theory) {
		final Term[] literals = new Term[mLiterals.length];
		for (int i = 0; i < mLiterals.length; ++i) {
			literals[i] = mLiterals[i].getSMTFormula(theory);
		}
		return literals;
	}

	public ProofLiteral[] toProofLiterals(ProofRules proofRules) {
		final ProofLiteral[] proofLits = new ProofLiteral[mLiterals.length];
		for (int i = 0; i < proofLits.length; i++) {
			final Literal lit = mLiterals[i];
			proofLits[i] = new ProofLiteral(lit.getAtom().getSMTFormula(proofRules.getTheory()), lit == lit.getAtom());
		}
		return proofLits;
	}
}
