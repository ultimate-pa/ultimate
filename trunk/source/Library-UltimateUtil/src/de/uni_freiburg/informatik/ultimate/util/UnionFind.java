/*
 * Copyright (C) 2009-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Utils Library.
 *
 * The ULTIMATE Utils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Utils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Utils Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Utils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Utils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;


/**
 * Data structure that can be used to partition a set of elements <E>.
 * http://en.wikipedia.org/wiki/Disjoint-set_data_structure
 * Each equivalence class has a unique representative. This implementation uses
 * HashMaps 
 * - to store for each element its equivalence class and
 * - to store for each equivalence class the representative
 * 
 * @author Matthias Heizmann
 */
public class UnionFind<E> {
	/**
	 * Maps an element to its equivalence class.
	 */
	Map<E,Set<E>> m_EquivalenceClass = new HashMap<E,Set<E>>();
	/**
	 * Maps an equivalence class to its representative.
	 */
	Map<Set<E>,E> m_Representative = new HashMap<Set<E>,E>();

	/**
	 * Returns the representative of the equivalence class of element e.
	 */
	public E find(E e) {
		Set<E> set = m_EquivalenceClass.get(e);
		return m_Representative.get(set);
	}

	/**
	 * Construct a new equivalence class that is a singleton and contains only
	 * element e.
	 */
	public void makeEquivalenceClass(E e) {
		if (m_EquivalenceClass.containsKey(e)) {
			throw new IllegalArgumentException("Already contained " + e);
		}
		Set<E> result = new HashSet<E>();
		result.add(e);
		m_EquivalenceClass.put(e, result);
		m_Representative.put(result, e);
	}

	/**
	 * Merge the equivalence classes of the elements e1 and e2. (e1 and e2 do 
	 * not have to be the representatives of this equivalence classes).
	 */
	public void union(E e1, E e2) {
		Set<E> set1 = m_EquivalenceClass.get(e1);
		Set<E> set2 = m_EquivalenceClass.get(e2);
		E set1rep = m_Representative.get(set1);
		m_Representative.remove(set1);
		m_Representative.remove(set2);
		set1.addAll(set2);
		for (E e : set2) {
			m_EquivalenceClass.put(e, set1);
		} 
		m_Representative.put(set1, set1rep);
	}
	
	/**
	 * Return collection of all elements e such that e is representative of an
	 * equivalence class.
	 */
	public Collection<E> getAllRepresentatives() {
		return m_Representative.values();
	}

	/**
	 * Return set of all elements that are in the same equivalence class than e.
	 * (Returned set also contains e).
	 */
	public Set<E> getEquivalenceClassMembers(E e) {
		return Collections.unmodifiableSet(m_EquivalenceClass.get(e));
	}

	@Override
	public String toString() {
		return m_Representative.toString();
	}


}

