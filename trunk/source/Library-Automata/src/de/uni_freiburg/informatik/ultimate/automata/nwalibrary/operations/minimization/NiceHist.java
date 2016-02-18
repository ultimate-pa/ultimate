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


/**
 * Utility functions for history states
 *
 * @author stimpflj
 *
 */
public class NiceHist implements Comparable<NiceHist> {
	/** linear state */
	int lin;

	/** hierarchical (history) state */
	int hier;


	public NiceHist() {}

	public NiceHist(int lin, int hier)
		{ this.lin = lin; this.hier = hier; }

	public boolean equals(NiceHist b)
		{ return lin == b.lin && hier == b.hier; }

	@Override
	public int hashCode()
		{ return 31 * lin + hier; }

	@Override
	public int compareTo(NiceHist b)
		{ return NiceHist.compareLinHier(this, b); }


	public static int compareLinHier(NiceHist a, NiceHist b) {
		if (a.lin != b.lin) return a.lin - b.lin;
		return a.hier - b.hier;
	}

	/**
	 * @param nwa
	 * @param history An array of NiceHist sorted by linear, then hierarchical states
	 * @return whether <code>history</code> is consistent with <code>nwa</code>
	 */
	public static boolean checkHistoryStatesConsistency(NiceNWA nwa, NiceHist[] hist) {
		for (int i = 0; i < hist.length; i++) {
			if (i != 0 && NiceHist.compareLinHier(hist[i],  hist[i-1]) <= 0)
				return false;
			if (hist[i].lin < 0 || hist[i].lin >= nwa.numStates)
				return false;
			if (hist[i].hier < 0 || hist[i].hier >= nwa.numStates)
				return false;
		}
		return true;
	}
}
