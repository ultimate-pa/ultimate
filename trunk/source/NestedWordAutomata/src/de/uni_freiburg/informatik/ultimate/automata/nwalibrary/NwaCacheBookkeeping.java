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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;


/**
 * If you write a nested word automaton that compute its transitions on demand,
 * then use this class to store which transitions are already computed.
 * 
 * Use this together with NestedWordAutomatonCache.
 * Problem solved by this class: Assume you query an on demand build automaton
 * for a transition, the automaton checks its cache an returns null.
 * Does this mean there is no such transition or does this mean the transition
 * was not yet computed? If you want to distinguish both cases you have to do
 * some bookkeeping to remember which transition have been already computed.
 * 
 * @author Matthias Heizmann
 */
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
