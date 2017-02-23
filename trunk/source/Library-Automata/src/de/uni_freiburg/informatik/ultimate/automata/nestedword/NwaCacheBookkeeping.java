/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * If you write a nested word automaton that computes its transitions on demand,
 * then use this class to store which transitions have already been computed.
 * <p>
 * Use this together with {@link NestedWordAutomatonCache}.<br>
 * Problem solved by this class: Assume you query an on-demand built automaton
 * for a transition, the automaton checks its cache and returns null.
 * Does this mean there is no such transition or does this mean the transition
 * was not yet computed? If you want to distinguish both cases, you have to do
 * some bookkeeping to remember which transitions have already been computed.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class NwaCacheBookkeeping<LETTER, STATE> {
	private static final String ADDED_TO_CACHE_TWICE = "The letter was added to the cache twice.";

	private final Map<STATE, Set<LETTER>> mCachedInternal = new HashMap<>();
	private final Map<STATE, Set<LETTER>> mCachedCall = new HashMap<>();
	private final Map<STATE, Map<STATE, Set<LETTER>>> mCachedReturn = new HashMap<>();

	/**
	 * Checks whether an internal transition has been computed.
	 * 
	 * @param state
	 *            state
	 * @param letter
	 *            letter
	 * @return true iff this transition has already been computed
	 */
	public boolean isCachedInternal(final STATE state, final LETTER letter) {
		final Set<LETTER> cbs = mCachedInternal.get(state);
		if (cbs == null) {
			return false;
		}
		return cbs.contains(letter);
	}

	/**
	 * Checks whether a call transition has been computed.
	 * 
	 * @param state
	 *            state
	 * @param letter
	 *            letter
	 * @return true iff this transition has already been computed
	 */
	public boolean isCachedCall(final STATE state, final LETTER letter) {
		final Set<LETTER> cbs = mCachedCall.get(state);
		if (cbs == null) {
			return false;
		}
		return cbs.contains(letter);
	}

	/**
	 * Checks whether a return transition has been computed.
	 * 
	 * @param state
	 *            state
	 * @param hier
	 *            hierarchical predecessor state
	 * @param letter
	 *            letter
	 * @return true iff this transition has already been computed
	 */
	public boolean isCachedReturn(final STATE state, final STATE hier, final LETTER letter) {
		final Map<STATE, Set<LETTER>> hier2cbs = mCachedReturn.get(state);
		if (hier2cbs == null) {
			return false;
		}
		final Set<LETTER> cbs = hier2cbs.get(hier);
		if (cbs == null) {
			return false;
		}
		return cbs.contains(letter);
	}

	/**
	 * Reports that all internal transitions have been computed.
	 * 
	 * @param state
	 *            state
	 * @param letter
	 *            letter
	 */
	public void reportCachedInternal(final STATE state, final LETTER letter) {
		Set<LETTER> cbs = mCachedInternal.get(state);
		if (cbs == null) {
			cbs = new HashSet<>();
			mCachedInternal.put(state, cbs);
		}
		final boolean modified = cbs.add(letter);
		assert modified : ADDED_TO_CACHE_TWICE;
	}

	/**
	 * Reports that all call transitions have been computed.
	 * 
	 * @param state
	 *            state
	 * @param letter
	 *            letter
	 */
	public void reportCachedCall(final STATE state, final LETTER letter) {
		Set<LETTER> cbs = mCachedCall.get(state);
		if (cbs == null) {
			cbs = new HashSet<>();
			mCachedCall.put(state, cbs);
		}
		final boolean modified = cbs.add(letter);
		assert modified : ADDED_TO_CACHE_TWICE;
	}

	/**
	 * Reports that all return transitions have been computed.
	 * 
	 * @param state
	 *            state
	 * @param hier
	 *            hierarchical predecessor state
	 * @param letter
	 *            letter
	 */
	public void reportCachedReturn(final STATE state, final STATE hier, final LETTER letter) {
		Map<STATE, Set<LETTER>> hier2cbs = mCachedReturn.get(state);
		if (hier2cbs == null) {
			hier2cbs = new HashMap<>();
			mCachedReturn.put(state, hier2cbs);
		}
		Set<LETTER> cbs = hier2cbs.get(hier);
		if (cbs == null) {
			cbs = new HashSet<>();
			hier2cbs.put(hier, cbs);
		}
		final boolean modified = cbs.add(letter);
		assert modified : ADDED_TO_CACHE_TWICE;
	}
}
