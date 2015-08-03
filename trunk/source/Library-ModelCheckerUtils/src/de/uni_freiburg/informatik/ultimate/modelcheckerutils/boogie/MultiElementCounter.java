/*
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Model Checker Utils Library.
 *
 * The ULTIMATE Model Checker Utils Library is free software: you can 
 * redistribute it and/or modify it under the terms of the GNU Lesser General 
 * Public License as published by the Free Software Foundation, either 
 * version 3 of the License, or (at your option) any later version.
 *
 * The ULTIMATE Model Checker Utils Library is distributed in the hope that it
 * will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty 
 * of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Model Checker Utils Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Model Checker Utils Library, or any covered work, 
 * by linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE Model Checker Utils Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.util.HashMap;
import java.util.Map;

/**
 * Counter that stores one number for each given object of type E.
 * Given the object you may increase the corresponding number by one.
 * Counting starts with 0.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <E>
 */
public class MultiElementCounter<E> {
	private final Map<E, Integer> m_Counter = new HashMap<E, Integer>();
	
	/**
	 * Increase the counter for element by one and return the 
	 * increased number.
	 */
	public Integer increase(E element) {
		final Integer lastIndex = m_Counter.get(element);
		final Integer newIndex;
		if (lastIndex == null) {
			newIndex = 1;
		} else {
			newIndex = lastIndex + 1;
		}
		m_Counter.put(element, newIndex);
		return newIndex;
	}
}
