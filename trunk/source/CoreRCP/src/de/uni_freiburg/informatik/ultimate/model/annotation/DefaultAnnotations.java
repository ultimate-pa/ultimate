/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.model
 * File:	DefaultAnnotations.java created on Mar 7, 2010 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.model.annotation;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * DefaultAnnotations
 *
 * @author Björn Buchhold
 *
 */
public class DefaultAnnotations implements IAnnotations {

	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -3930174445763628926L;
	private Map<String, Object> m_Map = new HashMap<String, Object>();
	

	public Object get(String key) {
		return this.m_Map.get(key);
	}

	public Map<String, Object> getAnnotationsAsMap() {
		return this.m_Map;
	}

	public void put(String key, Object value) {
		this.m_Map.put(key, value);
	}

	public Set<String> keySet() {
		return this.m_Map.keySet();
	}

	public boolean containsKey(String key) {
		return this.m_Map.containsKey(key);
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return this.m_Map.toString();
	}

}
