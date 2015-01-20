package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.Tuple;

/**
 * Helper Task for processing information from the Hopcroft algorithm for the
 * Incremental algorithm
 * 
 * @author layla
 *
 */
public class HelpIncremental implements Runnable {
	private MinimizeDfaAmrParallel<?, ?> m_incrementalAlgorithm;
	private int[] m_array1;
	private int[] m_array2;

	/**
	 * For each pair (a, b) of states where w.l.o.g. a in array1, b in array2 we
	 * know that a and b are not in the same equivalence class.
	 * 
	 * @param incremental
	 *            Currently running instance of the incremental algorithm
	 * @param array1
	 * @param array2
	 */
	public HelpIncremental(MinimizeDfaAmrParallel<?, ?> incremental,
			int[] array1, int[] array2) {
		m_incrementalAlgorithm = incremental;
		m_array1 = array1;
		m_array2 = array2;
	}

	@Override
	public void run() {
		Set<Tuple> neq = m_incrementalAlgorithm.getNeq();
		for (int i = 0; i < m_array1.length; i++) {
			for (int j = 0; j < m_array2.length; j++) {
				// Write into m_neq
				Tuple tuple;
				if (m_array1[i] < m_array2[j]) {
					tuple = new Tuple(m_array1[i], m_array2[j]);
				} else {
					tuple = new Tuple(m_array2[j], m_array1[i]);
				}
				synchronized (neq) {
					if (!neq.contains(tuple)) {
						((Set<Tuple>) neq).add(tuple);
					}
				}

			}
		}

	}

}
