package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

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