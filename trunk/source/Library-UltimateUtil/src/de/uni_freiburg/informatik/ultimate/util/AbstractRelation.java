/*
 * Copyright (C) 2009-2014 University of Freiburg
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

import java.util.Collections;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

/**
 * Object that represents a binary relation (i.e. a set of ordered pairs).
 * Given an element of this relation (d,r)
 * <ul>
 * <li> we call the first entry d the domain element of relation, and
 * <li> we call the second entry r the range element of the relation.
 * </ul>
 * We use a Map from domain elements to sets of range elements to store this
 * relation. Therefore we can directly get
 * <ul> 
 * <li> the set of all domain elements and
 * <li> the set of all range elements for a given domain element.
 * </ul>
 * This is an abstract class that does not define which Map data structure is
 * used.
 *  
 * 
 * @author Matthias Heizmann
 *
 * @param <D> Type of the elements that are in the domain of the relation.
 * @param <R> Type of the elements that are in the range of the relation.
 * @param <MAP> Type of Map that is used to store the relation.
 */
public abstract class AbstractRelation<D,R,MAP extends Map<D,Set<R>>> {
	protected final MAP m_Map;
	
	protected abstract MAP newMap();
	
	protected abstract Set<R> newSet();

	public AbstractRelation() {
		super();
		m_Map = newMap();
	}
	
	/**
	 * Add a pair (domainElem, rangeElem) to the relation.
	 * @return if this relation did not already contain the specified pair. 
	 */
	public boolean addPair(D domainElem, R rangeElem) {
		Set<R> rangeElems = m_Map.get(domainElem);
		if (rangeElems == null) {
			rangeElems = newSet();
			m_Map.put(domainElem, rangeElems);
		}
		return rangeElems.add(rangeElem);
	}

	/**
	 * Remove the pair (domainElem, rangeElem) from the relation.
	 * @return true if the set contained the specified pair. 
	 */
	public boolean removePair(D domainElem, R rangeElem) {
		final boolean result;
		Set<R> rangeElems = m_Map.get(domainElem);
		if (rangeElems == null) {
			result = false;
		} else {
			result = rangeElems.remove(rangeElems);
			if (rangeElems.isEmpty()) {
				m_Map.remove(domainElem);
			}
		}
		return result;
	}

	/**
	 * Add all elements contained in relation rel to this relation.
	 * Does not reuse sets of the relation rel but constructs new sets if 
	 * necessary.
	 */
	public void addAll(AbstractRelation<D,R,?> rel) {
		for (Entry<D, Set<R>> entry : rel.m_Map.entrySet()) {
			Set<R> rangeElems = m_Map.get(entry.getKey());
			if (rangeElems == null) {
				rangeElems = newSet();
				m_Map.put(entry.getKey(), rangeElems);
			}
			rangeElems.addAll(entry.getValue());
		}
	}
	
	/**
	 * @return true if the pair (domainElem, rangeElem) is contained in the
	 * relation.
	 */
	public boolean containsPair(D domainElem, R rangeElem) {
		Set<R> rangeElems = m_Map.get(domainElem);
		if (rangeElems == null) {
			return false;
		} else {
			return rangeElems.contains(rangeElem);
		}
	}
	
	/**
	 * Returns the set of all elements d such that for some r the pair
	 * (d,r) is in the relation.
	 */
	public Set<D> getDomain() {
		return m_Map.keySet();
	}
	
	/**
	 * Returns the set of all elements r such that for a the given element
	 * domainElem, the pair (domainElem, r) is in the relation.
	 */
	public Set<R> getImage(D domainElem) {
		Set<R> set = m_Map.get(domainElem);
		if (set == null) {
			return null;
		} else {
			return Collections.unmodifiableSet(m_Map.get(domainElem));
		}
	}
	
	/**
	 * Returns the number of all pairs contained in this relation.
	 */
	public int size() {
		int result = 0;
		for (Set<R> rangeSet : m_Map.values()) {
			result += rangeSet.size();
		}
		return result;
	}
	
	
	/**
	 * Returns the number of pairs (d,r) such that the first entry d
	 * coincides with the parameter domainElem.
	 */
	public int numberofPairsWithGivenDomainElement(D domainElem) {
		if (getDomain().contains(domainElem)) {
			return getImage(domainElem).size();
		} else {
			return 0;
		}
	}
	
	@Override
	public String toString() {
		return m_Map.toString();
	}
}
