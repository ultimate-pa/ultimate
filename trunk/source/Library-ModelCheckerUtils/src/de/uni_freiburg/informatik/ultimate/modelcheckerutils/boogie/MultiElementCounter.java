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
	Integer increase(E element) {
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
