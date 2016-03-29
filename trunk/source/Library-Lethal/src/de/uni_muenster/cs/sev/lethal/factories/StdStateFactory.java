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
package de.uni_muenster.cs.sev.lethal.factories;

import java.lang.ref.WeakReference;
import java.util.HashMap;

import de.uni_muenster.cs.sev.lethal.states.NamedState;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAOps;

/**
 * Gives some standard methods to create new states
 * which can be used by tree automata. <br>
 * In {@link GenFTAOps} different methods for creating states are used.
 * 
 * @author Martin, Irene, Philipp
 */
public class StdStateFactory extends StateFactory {
	
	/**Counter for anonymous states.*/
	private static int anonCount = 0;
	
	/**
	 * Stores the references to known named states. <br>
	 * Named states have a name of arbitrary type which is used as hash key.<br>
	 * They are stored separately from other states to avoid a mix-up of states and their names,
	 * since states can be used as names of states, too.
	 */
	private static HashMap<Object,WeakReference<NamedState<?>>> namedStateCache = new HashMap<Object,WeakReference<NamedState<?>>>();

	
	/**
	 * @see de.uni_muenster.cs.sev.lethal.factories.StateFactory#makeState()
	 */
	@Override
	public NamedState<String> makeState() {

		while (namedStateCache.containsKey("anon"+anonCount)){
			anonCount++;
		}

		final String id = "anon"+anonCount;
		anonCount++;
		return new NamedState<String>(id);
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.factories.StateFactory#makeState(java.lang.Object)
	 */
	@Override
	public <T> NamedState<T> makeState(T name) {
		return create(name);
	}


	/**
	 * Creates a new named state with the given name.
	 * 
	 * @param <T> type of the name of a state
	 * @param name name of the new state
	 * @return a new named state
	 */
	@SuppressWarnings("unchecked")
	private <T> NamedState<T> create(T name) {
		WeakReference<NamedState<?>> ref = namedStateCache.get(name); //lookup if we know this state

		// this cast is safe because if we find a NamedState for
		// the name, its type parameter is the type of the name
		NamedState<T> s = (ref!=null)?(NamedState<T>)ref.get():null;
		if (s==null) {
			s = new NamedState<T>(name);
			namedStateCache.put(name, new WeakReference<NamedState<?>>(s));
			return s;
		} else {
			return s;
		}
	}

}
