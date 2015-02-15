/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

/**
 * Maps elements of an Iterable to the number of its occurrence.
 * Visualizes this in a sorted array that lists the occurrences of each element.
 * @author Matthias Heizmann
 *
 * @param <E>
 */
public class HistogramOfIterable<E> {
	private final Iterable<E> m_Iterable;
	private final Map<E, Integer> m_HistogramMap;
	private final Integer[] m_VisualizationArray;
	
	
	public HistogramOfIterable(Iterable<E> iterable) {
		super();
		m_Iterable = iterable;
		m_HistogramMap = generateHistogramMap(m_Iterable);
		m_VisualizationArray = generateVisualizationArray(m_HistogramMap);
	}

	private Integer[] generateVisualizationArray(Map<E, Integer> histogramMap) {
		Integer[] result = histogramMap.values().toArray(new Integer[histogramMap.size()]);
		Arrays.sort(result, Collections.reverseOrder());
		return result;
	}
	
	@Override
	public String toString() {
		return Arrays.toString(m_VisualizationArray);
	}

	public static <E> Map<E, Integer> generateHistogramMap(Iterable<E> iterable) {
		Map<E, Integer> result = new HashMap<E, Integer>();
		for (E e : iterable) {
			if (result.containsKey(e)) {
				result.put(e, Integer.valueOf(result.get(e).intValue()+1));
			} else {
				result.put(e, 1);
			}
		}
		return result;
	}
	
	
	

}
