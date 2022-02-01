/*
 * Copyright (C) 2016 Jens Stimpfle <stimpflj@informatik.uni-freiburg.de>

 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 3 of the License,
 * or (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be
 * useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser
 * General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see
 * <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automata Library, or any covered work, by linking or combining it
 * with Eclipse RCP (or a modified version of Eclipse RCP), containing parts
 * covered by the terms of the Eclipse Public License, the licensors of the
 * ULTIMATE Automata Library grant you additional permission to convey the
 * resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.arrays;

import java.util.ArrayList;
import java.util.HashSet;

/**
 * A Nested Word automaton. There is no distinction between linear and hierarchical states.
 * <p>
 * This is a mostly normalized POD (plain old data) representation of NWAs.
 * <p>
 * The following constraints are useful in most situations:
 * <ul>
 * <li>numStates &ge; 0 && numISyms &ge; 0 && numRSyms &ge; 0
 * <li>isInitial &ne; null && isInitial.length = numStates
 * <li>isFinal &ne; null && isFinal.length = numStates
 * <li>iTrans, cTrans, rTrans are not null and use only symbols and states from the ranges [0, numStates), [0,
 * numISyms), [0, numCSyms), [0, numRSyms)
 * </ul>
 * <p>
 * This class has static methods to verify these constraints, and also methods to assert determinism.
 *
 * @author stimpflj
 */
final class NwaWithArrays implements Cloneable {
	/** Number of states */
	int mNumStates;

	/** Number of internal symbols */
	int mNumISyms;

	/** Number of call symbols */
	int mNumCSyms;

	/** Number of return symbols */
	int mNumRSyms;

	/** For each state whether it is initial */
	boolean[] mIsInitial;

	/** For each state whether it is final */
	boolean[] mIsFinal;

	/** Internal Transitions */
	ITrans[] mITrans;

	/** Call Transitions */
	CTrans[] mCTrans;

	/** Return Transitions */
	RTrans[] mRTrans;

	/**
	 * @param nwa
	 *            readonly <code>NWA</code>
	 * @return <code>true</code> iff the automaton is consistent
	 */
	static boolean checkConsistency(final NwaWithArrays nwa) {
		if (nwa.mNumStates < 0) {
			return false;
		}
		if (nwa.mNumISyms < 0) {
			return false;
		}
		if (nwa.mNumRSyms < 0) {
			return false;
		}
		if (nwa.mNumCSyms < 0) {
			return false;
		}

		if (nwa.mIsInitial == null || nwa.mIsInitial.length != nwa.mNumStates) {
			return false;
		}
		if (nwa.mIsFinal == null || nwa.mIsFinal.length != nwa.mNumStates) {
			return false;
		}

		for (final ITrans x : nwa.mITrans) {
			if (x.mSrc < 0 || x.mSrc >= nwa.mNumStates) {
				return false;
			}
			if (x.mSym < 0 || x.mSym >= nwa.mNumISyms) {
				return false;
			}
			if (x.mDst < 0 || x.mDst >= nwa.mNumStates) {
				return false;
			}
		}
		for (final CTrans x : nwa.mCTrans) {
			if (x.mSrc < 0 || x.mSrc >= nwa.mNumStates) {
				return false;
			}
			if (x.mSym < 0 || x.mSym >= nwa.mNumCSyms) {
				return false;
			}
			if (x.mDst < 0 || x.mDst >= nwa.mNumStates) {
				return false;
			}
		}
		for (final RTrans x : nwa.mRTrans) {
			if (x.mSrc < 0 || x.mSrc >= nwa.mNumStates) {
				return false;
			}
			if (x.mSym < 0 || x.mSym >= nwa.mNumRSyms) {
				return false;
			}
			if (x.mTop < 0 || x.mTop >= nwa.mNumStates) {
				return false;
			}
			if (x.mDst < 0 || x.mDst >= nwa.mNumStates) {
				return false;
			}
		}

		return true;
	}

	/**
	 * @param nwa
	 *            readonly <code>NWA</code> which is consistent as by <code>checkConsistency()</code>
	 * @return <code>true</code> iff the automaton is deterministic (multiple identical transitions count as
	 *         non-deterministic)
	 */
	static boolean checkDeterminism(final NwaWithArrays nwa) {
		final HashSet<ITrans> iSeen = new HashSet<ITrans>();
		for (final ITrans x : nwa.mITrans) {
			if (!iSeen.add(new ITrans(x.mSrc, x.mSym, 0))) {
				return false;
			}
		}
		final HashSet<CTrans> cSeen = new HashSet<CTrans>();
		for (final CTrans x : nwa.mCTrans) {
			if (!cSeen.add(new CTrans(x.mSrc, x.mSym, 0))) {
				return false;
			}
		}
		final HashSet<RTrans> rSeen = new HashSet<RTrans>();
		for (final RTrans x : nwa.mRTrans) {
			if (!rSeen.add(new RTrans(x.mSrc, x.mSym, x.mTop, 0))) {
				return false;
			}
		}

		return true;
	}

	/**
	 * @param nwa
	 *            a NWA which is consistent as by checkConsistency()
	 * @return ArrayList containing all final states of <code>nwa</code>, in strictly ascending order.
	 */
	static ArrayList<Integer> computeInitialStates(final NwaWithArrays nwa) {
		final ArrayList<Integer> out = new ArrayList<Integer>();

		for (int i = 0; i < nwa.mNumStates; i++) {
			if (nwa.mIsInitial[i]) {
				out.add(i);
			}
		}

		return out;
	}

	/**
	 * @param nwa
	 *            an NWA which is consistent as by checkConsistency
	 * @return ArrayList containing all final states of <code>nwa</code>, in strictly ascending order.
	 */
	static ArrayList<Integer> computeFinalStates(final NwaWithArrays nwa) {
		final ArrayList<Integer> out = new ArrayList<Integer>();

		for (int i = 0; i < nwa.mNumStates; i++) {
			if (nwa.mIsFinal[i]) {
				out.add(i);
			}
		}

		return out;
	}

	/**
	 * @return A copy of this NWA instance. No references are shared with the instance on which this method is called.
	 */
	@Override
	public NwaWithArrays clone() {
		final NwaWithArrays out = new NwaWithArrays();
		out.mNumStates = mNumStates;
		out.mNumISyms = mNumISyms;
		out.mNumCSyms = mNumCSyms;
		out.mNumRSyms = mNumRSyms;
		out.mIsInitial = mIsInitial.clone();
		out.mIsFinal = mIsFinal.clone();
		out.mITrans = mITrans.clone();
		out.mCTrans = mCTrans.clone();
		out.mRTrans = mRTrans.clone();

		return out;
	}
}

/**
 * Call transition for nested word automata (NWA).
 *
 * @author stimpflj
 */
final class ITrans {
	/** Source state */
	int mSrc;

	/** Internal symbol */
	int mSym;

	/** Destination state */
	int mDst;

	ITrans() {
	}

	ITrans(final int src, final int sym, final int dst) {
		mSrc = src;
		mSym = sym;
		mDst = dst;
	}

	@Override
	public boolean equals(final Object obj) {
		if (obj == null || !(obj instanceof ITrans)) {
			return false;
		}

		final ITrans b = (ITrans) obj;
		return mSrc == b.mSrc && mSym == b.mSym && mDst == b.mDst;
	}

	@Override
	public int hashCode() {
		return (mSrc * 31 + mSym) * 31 + mDst;
	}

	static int compareSrcSymDst(final ITrans a, final ITrans b) {
		if (a.mSrc != b.mSrc) {
			return a.mSrc - b.mSrc;
		}
		if (a.mSym != b.mSym) {
			return a.mSym - b.mSym;
		}
		return a.mDst - b.mDst;
	}
}

/**
 * Call transition for nested word automata (NWA)
 *
 * @author stimpflj
 */
final class CTrans {
	/** Source state */
	int mSrc;

	/** Call symbol */
	int mSym;

	/** Destination state */
	int mDst;

	CTrans() {
	}

	CTrans(final int src, final int sym, final int dst) {
		mSrc = src;
		mSym = sym;
		mDst = dst;
	}

	@Override
	public boolean equals(final Object obj) {
		if (obj == null || !(obj instanceof CTrans)) {
			return false;
		}

		final CTrans b = (CTrans) obj;

		return mSrc == b.mSrc && mSym == b.mSym && mDst == b.mDst;
	}

	@Override
	public int hashCode() {
		return (mSrc * 31 + mSym) * 31 + mDst;
	}

	static int compareSrcSymDst(final CTrans a, final CTrans b) {
		if (a.mSrc != b.mSrc) {
			return a.mSrc - b.mSrc;
		}
		if (a.mSym != b.mSym) {
			return a.mSym - b.mSym;
		}
		return a.mDst - b.mDst;
	}
}

/**
 * Return transition for nested word automata (NWA).
 *
 * @author stimpflj
 */
final class RTrans {
	/** Source state */
	int mSrc;

	/** Return symbol */
	int mSym;

	/** top-of-stack (hierarchical) state */
	int mTop;

	/** Destination state */
	int mDst;

	RTrans() {
	}

	RTrans(final int src, final int sym, final int top, final int dst) {
		mSrc = src;
		mSym = sym;
		mTop = top;
		mDst = dst;
	}

	@Override
	public boolean equals(final Object obj) {
		if (!(obj instanceof RTrans)) {
			return false;
		}

		final RTrans b = (RTrans) obj;

		return mSrc == b.mSrc && mTop == b.mTop && mSym == b.mSym && mDst == b.mDst;
	}

	@Override
	public int hashCode() {
		return ((mSrc * 31 + mSym) * 31 + mTop) * 31 + mDst;
	}

	static int compareSrcSymTopDst(final RTrans a, final RTrans b) {
		if (a.mSrc != b.mSrc) {
			return a.mSrc - b.mSrc;
		}
		if (a.mSym != b.mSym) {
			return a.mSym - b.mSym;
		}
		if (a.mTop != b.mTop) {
			return a.mTop - b.mTop;
		}
		return a.mDst - b.mDst;
	}

	static int compareSrcTopSymDst(final RTrans a, final RTrans b) {
		if (a.mSrc != b.mSrc) {
			return a.mSrc - b.mSrc;
		}
		if (a.mTop != b.mTop) {
			return a.mTop - b.mTop;
		}
		if (a.mSym != b.mSym) {
			return a.mSym - b.mSym;
		}
		return a.mDst - b.mDst;
	}
}
