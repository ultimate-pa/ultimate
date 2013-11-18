package de.uni_freiburg.informatik.ultimate.automata;

import java.util.Collections;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.NavigableSet;
import java.util.Set;
import java.util.TreeMap;

public class TreeRelation<D,R> {
	
	private final TreeMap<D,HashSet<R>> m_Map = new TreeMap<D,HashSet<R>>();
	
	

	public void addPair(D domainElem, R rangeElem) {
		HashSet<R> rangeElems = m_Map.get(domainElem);
		if (rangeElems == null) {
			rangeElems = new HashSet<R>();
			m_Map.put(domainElem, rangeElems);
		}
		rangeElems.add(rangeElem);
	}
	
	public void addAll(TreeRelation<D,R> hr) {
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
		Set<R> result = m_Map.get(domainElem);
		if (result == null) {
			result = Collections.emptySet();
		}
		return result;
	}
	
	public int size() {
		int result = 0;
		for (HashSet<R> rangeSet : m_Map.values()) {
			result += rangeSet.size();
		}
		return result;
	}

	public NavigableSet<D> descendingDomain() {
		return m_Map.descendingKeySet();
	}
	
	
	
	

}
