package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Queue;

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
	private int m_state2;

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
			final MinimizeDfaHopcroftParallel<?, ?> hopcroft,
			final int state1, final int state2) {
		m_incrementalAlgorithm = incremental;
		m_hopcroftAlgorithm = hopcroft;
		m_state1 = state1;
		m_state2 = state2;
	}

	@Override
	public void run() {
		ArrayList<Integer> setToRemove = null;

		// If a set in partition of Hopcroft contains state1 and state2 check
		// whether all states in that set are equivalent.
		Queue<ArrayList<Integer>> setList = m_hopcroftAlgorithm.getSetList();
		// Return in case of empty set list.
		if (setList.isEmpty()) {
			return;
		}
		synchronized (setList) {
			for (ArrayList<Integer> set : setList) {
				if (set == null) {
					continue;
				}
				if (set.contains(m_state1) && set.contains(m_state2)) {
					boolean eq = true;
					for (int i = 0; i < set.size() - 1 && eq; i++) {
						for (int j = i + 1; j < set.size() && eq; j++) {
							if (m_incrementalAlgorithm.find(set.get(i)) != m_incrementalAlgorithm
									.find(set.get(j))) {
								eq = false;
							}
						}
					}
					if (eq) {
						setToRemove = set;
						Queue<ArrayList<Integer>> partitions = m_hopcroftAlgorithm
								.getFinalPartitions();
						if (partitions != null) {
							partitions.add(set);
						}
					}

				}
			}
			if (setToRemove != null) {
				setList.remove(setToRemove);
			}
		}
	}
}