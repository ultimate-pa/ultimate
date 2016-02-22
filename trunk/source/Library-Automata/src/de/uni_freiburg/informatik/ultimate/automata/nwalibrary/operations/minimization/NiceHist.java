/*
 * Copyright (C) 2016 Jens Stimpfle <stimpflj@informatik.uni-freiburg.de>

 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.ArrayList;

/**
 * Utility functions for history states
 *
 * @author stimpflj
 *
 */
public class NiceHist {
	/** linear state */
	int lin;

	/** hierarchical (history) state */
	int hier;


	public NiceHist() {}

	public NiceHist(int lin, int hier) {
		this.lin = lin;
		this.hier = hier;
	}

	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof NiceHist))
			return false;
		NiceHist b = (NiceHist) obj;
		return lin == b.lin && hier == b.hier;
	}

	@Override
	public int hashCode() {
		return 31 * lin + hier;
	}

	public static int compareLinHier(NiceHist a, NiceHist b) {
		if (a.lin != b.lin) return a.lin - b.lin;
		return a.hier - b.hier;
	}

	/**
	 * @param nwa
	 *
	 * @param history An array of NiceHist sorted by linear, then hierarchical
	 * states
	 *
	 * @return whether <code>history</code> is consistent with <code>nwa</code>
	 * NOTE: history states can be -1. This means "bottom-of-stack" state.
	 */
	public static boolean checkHistoryStatesConsistency(NiceNWA nwa, ArrayList<NiceHist> hist) {
		for (int i = 0; i < hist.size(); i++) {
			if (hist.get(i).lin < 0 || hist.get(i).lin >= nwa.numStates)
				return false;
			if (hist.get(i).hier < -1 || hist.get(i).hier >= nwa.numStates)
				return false;
		}
		return true;
	}
}
