/*
 * Copyright (C) 2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Layla Franke
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.parallel;

import java.util.HashSet;
import java.util.Iterator;

/**
 * Helper Task for processing information from the Incremental algorithm for the
 * Hopcroft algorithm
 * 
 * @author layla
 *
 */
public class HelpHopcroft implements Runnable {
	private MinimizeDfaAmrParallel<?, ?> m_incrementalAlgorithm;
	private MinimizeDfaHopcroftParallel<?, ?> m_hopcroftAlgorithm;
	private int m_state1;

	/**
	 * The incremental algorithm determined, that state1 and state2 are of the
	 * same equivalence class.
	 * 
	 * @param incremental
	 *            Instance of incremental algorithm that creates the task
	 * @param hopcroft
	 *            Instance of currently parallel running Hopcroft algorithm
	 * @param state1
	 * @param state2
	 */
	public HelpHopcroft(final MinimizeDfaAmrParallel<?, ?> incremental,
			final MinimizeDfaHopcroftParallel<?, ?> hopcroft, final int state1,
			final int state2) {
		m_incrementalAlgorithm = incremental;
		m_hopcroftAlgorithm = hopcroft;
		m_state1 = state1;
	}

	@Override
	public void run() {
		// If a set in partition of Hopcroft contains state1 and state2 check
		// whether all states in that set are equivalent.
		HashSet<Integer> set = null;
		try {
			set = m_hopcroftAlgorithm.getBlock(m_state1);
		} catch (NullPointerException e) {
			return;
		}
		// Return in case of empty set list.
		if (set == null) {
			return;
		}
		boolean eq = true;
		assert (set.size() > 1);
		if (set.size() > 2) {
			for (Iterator<Integer> iter = set.iterator(); iter.hasNext();) {
				int elem = iter.next();

				int state1rep = m_incrementalAlgorithm.find(m_state1);
				if (m_incrementalAlgorithm.find(elem) != state1rep) {
					eq = false;
				}
			}
		}
		if (eq) {
			for (int state : set) {
				m_hopcroftAlgorithm.removePartition(state);
			}
		}
	}

}
