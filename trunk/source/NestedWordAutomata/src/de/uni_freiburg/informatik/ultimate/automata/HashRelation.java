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
	

}
