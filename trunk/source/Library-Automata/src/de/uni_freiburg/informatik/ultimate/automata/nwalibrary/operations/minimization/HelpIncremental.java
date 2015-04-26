package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

/**
 * Helper Task for processing information from the Hopcroft algorithm for the
 * Incremental algorithm
 * 
 * @author layla
 *
 */
public class HelpIncremental implements Runnable {
	private MinimizeDfaAmrParallel<?, ?> m_incrementalAlgorithm;
	private HashSet<Integer> m_array1;
	private HashSet<Integer> m_array2;

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
			HashSet<Integer> array1, HashSet<Integer> array2) {
		m_incrementalAlgorithm = incremental;
		m_array1 = array1;
		m_array2 = array2;
	}

	@Override
	public void run() {
		Set<Tuple> neq = m_incrementalAlgorithm.getNeq();
		for (Iterator<Integer> iter1 = m_array1.iterator(); iter1.hasNext();) {
			int i = iter1.next();
			for (Iterator<Integer> iter2 = m_array2.iterator(); iter2.hasNext();) {
				// Write into m_neq

				int j = iter2.next();

				Tuple tuple;
				if (i < j) {
					tuple = new Tuple(i, j);
				} else {
					tuple = new Tuple(j, i);
				}
				if (!neq.contains(tuple)) {
					((Set<Tuple>) neq).add(tuple);
				}
			}
		}

	}

}
