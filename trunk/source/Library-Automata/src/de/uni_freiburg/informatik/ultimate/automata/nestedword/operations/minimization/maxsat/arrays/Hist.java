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

/**
 * Utility functions for history states
 *
 * @author stimpflj
 */
final class Hist {
	/** linear state */
	int mLin;

	/** hierarchical (history) state */
	int mHier;

	Hist() {
	}

	Hist(final int lin, final int hier) {
		mLin = lin;
		mHier = hier;
	}

	@Override
	public boolean equals(final Object obj) {
		if (!(obj instanceof Hist)) {
			return false;
		}

		final Hist b = (Hist) obj;

		return mLin == b.mLin && mHier == b.mHier;
	}

	@Override
	public int hashCode() {
		return 31 * mLin + mHier;
	}

	static int compareLinHier(final Hist a, final Hist b) {
		if (a.mLin != b.mLin) {
			return a.mLin - b.mLin;
		}
		return a.mHier - b.mHier;
	}

	/**
	 * @return whether <code>history</code> is consistent with <code>nwa</code> NOTE: history states can be -1. This
	 *         means "bottom-of-stack" state.
	 */
	static boolean checkConsistency(final NwaWithArrays nwa, final ArrayList<Hist> hist) {
		for (int i = 0; i < hist.size(); i++) {
			if (hist.get(i).mLin < 0 || hist.get(i).mLin >= nwa.mNumStates) {
				return false;
			}
			if (hist.get(i).mHier < -1 || hist.get(i).mHier >= nwa.mNumStates) {
				return false;
			}
		}
		return true;
	}
}
