/*
 * Copyright 2009 Dorothea Jansen <d.jansen@uni-muenster.de>, Martin Mohr <mohrfrosch@uni-muenster.de>, Irene Thesing <i_thes01@uni-muenster.de>, Anton Reis <antonreis@gmx.de>, Maria Schatz <m_scha17@uni-muenster.de>, Philipp Claves <philipp.claves@uni-muenster.de>, Sezar Jarrous <sezar.jarrous@gmail.com>
 *
 * This file is part of LETHAL.
 *
 * LETHAL is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * LETHAL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with LETHAL.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal;

import de.uni_muenster.cs.sev.lethal.states.HedgeState;
import de.uni_muenster.cs.sev.lethal.states.State;

import java.util.HashSet;
import java.util.Set;
import java.util.WeakHashMap;

/**
 * This class implements a state cache. It is used to cache packed states for the
 * hedge automaton. The needed states are generated if needed and returned if
 * wanted.
 *
 * @author Anton, Maria
 */
public final class HedgeStateCache {
	private static final WeakHashMap<State, HedgeState<? extends State>> stateCache = new WeakHashMap<State, HedgeState<? extends State>>();

	private HedgeStateCache() {
		super();
	}

	/**
	 * Checks the cache for the transformed state, generates it if needed.
	 * Returns the transformed state.
	 *
	 * @param state the state to be transformed
	 * @param <G_State>   type of the state
	 * @return the transformed state
	 */
	@SuppressWarnings("unchecked")
	public static <G_State extends State> HedgeState<G_State> getState(final G_State state) {
		final HedgeState<G_State> ret;
		if (stateCache.containsKey(state)) {
			// this cast is safe, because the stored
			// hedge state has always the type of the state used as key
			ret = (HedgeState<G_State>) stateCache.get(state);
		} else {
			ret = new HedgeState<G_State>(state, null);
			stateCache.put(state, ret);
		}
		return ret;
	}

	/**
	 * Checks the cache for the transformed states, generates them if needed.
	 * Returns the transformed states
	 *
	 * @param states the states to be transformed
	 * @param <G_State>    type of the state
	 * @return the transformed states
	 */
	@SuppressWarnings("unchecked")
	public static <G_State extends State> Set<HedgeState<G_State>> getState(
			final Iterable<G_State> states) {
		final Set<HedgeState<G_State>> ret = new HashSet<HedgeState<G_State>>();
		for (final G_State state : states)
			if (stateCache.containsKey(state)) {
				// this cast is safe, because the stored
				// hedge state has always the type of the state used as key
				ret.add((HedgeState<G_State>) stateCache.get(state));
			} else {
				final HedgeState<G_State> temp = new HedgeState<G_State>(state, null);
				ret.add(temp);
				stateCache.put(state, temp);
			}
		return ret;
	}
}
