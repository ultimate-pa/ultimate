/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util;

import java.util.Comparator;

/**
 * Comparator for priorities in a priority game in which priorities 0, 1, and 2 are used.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class PriorityComparator implements Comparator<Integer> {

	/**
	 * Compares two priorities according to the order 0 > 2 > 1 (i.e., the "better-for-duplicator-order"). Throws an
	 * Exception if the priorities are not from the set {0,1,2}.
	 * 
	 * @return 1 if the lhs is better for duplicator, 0 if lhs und rhs are equal -1 if lhs is better for spoiler.
	 */
	@Override
	public int compare(final Integer lhs, final Integer rhs) {
		switch (lhs) {
			case 0: {
				switch (rhs) {
					case 0:
						return 0;
					case 1:
						return 1;
					case 2:
						return 1;
					default:
						throw new IllegalArgumentException("unsupported priority " + rhs);
				}
			}
			case 1: {
				switch (rhs) {
					case 0:
						return -1;
					case 1:
						return 0;
					case 2:
						return -1;
					default:
						throw new IllegalArgumentException("unsupported priority " + rhs);
				}
			}
			case 2: {
				switch (rhs) {
					case 0:
						return -1;
					case 1:
						return 1;
					case 2:
						return 0;
					default:
						throw new IllegalArgumentException("unsupported priority " + rhs);
				}
			}
			default:
				throw new IllegalArgumentException("unsupported priority " + lhs);
		}
	}

}
