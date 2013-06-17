package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;


public class NwaCacheBookkeeping<LETTER,STATE> {
	
	private final Map<STATE,Set<LETTER>> m_CachedInternal = new HashMap<STATE,Set<LETTER>>();
	private final Map<STATE,Set<LETTER>> m_CachedCall = new HashMap<STATE,Set<LETTER>>();
	private final Map<STATE,Map<STATE,Set<LETTER>>> m_CachedReturn = new HashMap<STATE,Map<STATE,Set<LETTER>>>();
	
	public boolean isCachedInternal(STATE state, LETTER letter) {
		Set<LETTER> cbs = m_CachedInternal.get(state);
		if (cbs == null) {
			return false;
		} else {
			return cbs.contains(letter);
		}
	}
	
	public boolean isCachedCall(STATE state, LETTER letter) {
		Set<LETTER> cbs = m_CachedCall.get(state);
		if (cbs == null) {
			return false;
		} else {
			return cbs.contains(letter);
		}
	}
	
	public boolean isCachedReturn(STATE state, STATE hier, LETTER letter) {
		Map<STATE, Set<LETTER>> hier2cbs = m_CachedReturn.get(state);
		if (hier2cbs == null) {
			return false;
		} else {
			Set<LETTER> cbs = hier2cbs.get(hier);
			if (cbs == null) {
				return false;
			} else {
				return cbs.contains(letter);
			}
		}
	}
	
	public void reportCachedInternal(STATE state, LETTER letter) {
		Set<LETTER> cbs = m_CachedInternal.get(state);
		if (cbs == null) {
			cbs = new HashSet<LETTER>();
			m_CachedInternal.put(state, cbs);
		}
		boolean modified = cbs.add(letter);
		assert modified : "added to cache twice";
	}
	
	public void reportCachedCall(STATE state, LETTER letter) {
		Set<LETTER> cbs = m_CachedCall.get(state);
		if (cbs == null) {
			cbs = new HashSet<LETTER>();
			m_CachedCall.put(state, cbs);
		}
		boolean modified = cbs.add(letter);
		assert modified : "added to cache twice";
	}
	
	public void reportCachedReturn(STATE state, STATE hier, LETTER letter) {
		Map<STATE, Set<LETTER>> hier2cbs = m_CachedReturn.get(state);
		if (hier2cbs == null) {
			hier2cbs = new HashMap<STATE, Set<LETTER>>();
			m_CachedReturn.put(state, hier2cbs);
		}
		Set<LETTER> cbs = hier2cbs.get(hier);
		if (cbs == null) {
			cbs = new HashSet<LETTER>();
			hier2cbs.put(hier, cbs);
		}
		boolean modified = cbs.add(letter);
		assert modified : "added to cache twice";
	}

}
