package de.uni_freiburg.informatik.ultimate.util;

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
	 * Add the element eNew to the equivalence class of element eContained.
	 * The element eNew must not be contained in this UnionFind data structure.
	 * The element eContained has to be contained in this UnionFind data 
	 * structure.
	 */
	public void add(E eNew, E eContained) {
		if (!m_EquivalenceClass.containsKey(eContained)) {
			throw new IllegalArgumentException("Not contained " + eContained);
		}
		if (m_EquivalenceClass.containsKey(eNew)) {
			throw new IllegalArgumentException("Already contained " + eContained);
		}
		Set<E> equivalenceClass = m_EquivalenceClass.get(eContained);
		equivalenceClass.add(eNew);
		m_EquivalenceClass.put(eNew, equivalenceClass);
	}
	
	/**
	 * Returns an unmodifiable set that contains the representatives of each
	 * equivalence class.
	 */
	public Set<E> getRepresentatives() {
		return Collections.unmodifiableSet(m_EquivalenceClass.keySet());
	}

	/**
	 * Returns an unmodifiable versions of the equivalence class of element e. 
	 */
	public Set<E> getEquivalenceClass(E e) {
		return Collections.unmodifiableSet(m_EquivalenceClass.get(e)); 
	}

	@Override
	public String toString() {
		return m_Representative.toString();
	}
}

