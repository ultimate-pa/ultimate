/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.util.HashMap;
import java.util.Set;
import java.util.TreeSet;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class RelationWithTreeSet<D, R> extends AbstractRelation<D, R, HashMap<D, Set<R>>> {

	@Override
	public HashMap<D, Set<R>> newMap() {
		return new HashMap<D, Set<R>>();
	}

	@Override
	public TreeSet<R> newSet() {
		return new TreeSet<R>();
	}

	@Override
	public Set<R> getImage(D domainElem) {
		return m_Map.get(domainElem);
	}


	
}
