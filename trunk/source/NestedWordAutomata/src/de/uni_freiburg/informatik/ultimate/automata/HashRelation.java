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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;

public class HashRelation<D,R> {
	
	private final HashMap<D,HashSet<R>> m_Map = new HashMap<D,HashSet<R>>();
	
	

	public void addPair(D domainElem, R rangeElem) {
		HashSet<R> rangeElems = m_Map.get(domainElem);
		if (rangeElems == null) {
			rangeElems = new HashSet<R>();
			m_Map.put(domainElem, rangeElems);
		}
		rangeElems.add(rangeElem);
	}
	
	public void addAll(HashRelation<D,R> hr) {
		for (Entry<D, HashSet<R>> entry : hr.m_Map.entrySet()) {
			HashSet<R> rangeElems = m_Map.get(entry.getKey());
			if (rangeElems == null) {
				rangeElems = new HashSet<R>();
				m_Map.put(entry.getKey(), rangeElems);
			}
			rangeElems.addAll(entry.getValue());
		}
	}
	
	public boolean containsPair(D domainElem, R rangeElem) {
		HashSet<R> rangeElems = m_Map.get(domainElem);
		if (rangeElems == null) {
			return false;
		} else {
			return rangeElems.contains(rangeElem);
		}
	}
	
	
	public Set<D> getDomain() {
		return m_Map.keySet();
	}
	
	public Set<R> getImage(D domainElem) {
		return m_Map.get(domainElem);
	}
	
	public int size() {
		int result = 0;
		for (HashSet<R> rangeSet : m_Map.values()) {
			result += rangeSet.size();
		}
		return result;
	}
	

}
