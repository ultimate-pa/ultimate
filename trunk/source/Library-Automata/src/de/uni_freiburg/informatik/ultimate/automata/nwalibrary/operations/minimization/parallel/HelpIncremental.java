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
import java.util.Set;

/**
 * Helper Task for processing information from the Hopcroft algorithm for the
 * Incremental algorithm
 * 
 * @author layla
 *
 */
public class HelpIncremental implements Runnable {
	private final MinimizeDfaAmrParallel<?, ?> mincrementalAlgorithm;
	private final HashSet<Integer> marray1;
	private final HashSet<Integer> marray2;

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
		mincrementalAlgorithm = incremental;
		marray1 = array1;
		marray2 = array2;
	}

	@Override
	public void run() {
		final Set<Tuple> neq = mincrementalAlgorithm.getNeq();
		for (final Iterator<Integer> iter1 = marray1.iterator(); iter1.hasNext();) {
			final int i = iter1.next();
			for (final Iterator<Integer> iter2 = marray2.iterator(); iter2.hasNext();) {
				// Write into mneq

				final int j = iter2.next();

				Tuple tuple;
				if (i < j) {
					tuple = new Tuple(i, j);
				} else {
					tuple = new Tuple(j, i);
				}
				if (!neq.contains(tuple)) {
					neq.add(tuple);
				}
			}
		}

	}

}
