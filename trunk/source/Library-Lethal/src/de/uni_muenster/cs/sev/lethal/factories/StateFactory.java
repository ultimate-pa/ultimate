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

import de.uni_muenster.cs.sev.lethal.states.NamedState;

/**
 * Provides some methods to create a new state, which is either entirely fresh or
 * created from an arbitrary object, which is used to identify it.
 * 
 * @author Martin, Irene, Philipp
 */
public abstract class StateFactory {
	
	private static StateFactory instance = null;
	
	/**
	 * Initially sets a non-standard state factory.
	 * @param factory the state factory to use.
	 */
	public static void init(StateFactory factory){
		assert(instance == null);
		instance = factory;
	}
	
	/**
	 * Returns the state factory instance.
	 * @return the state factory instance
	 */
	public static StateFactory getStateFactory(){
		if (instance == null) instance = new StdStateFactory();
		return instance;
	}
	
	
	/**
	 * Creates a new named state from the given name. This method must be implemented by subclasses.<br>
	 * Make sure, that the name does not change afterwards.
	 * 
	 * @param <T> type of name
	 * @param name name of the new state. <br> 
	 * WARNING: Once the name is stored in the StateFactory, it must not be changed!
	 * @return a fresh state with that name
	 */
	public abstract <T> NamedState<T> makeState(T name);
	
	/**
	 * Creates a new state out of hot air.
	 * 
	 * @return fresh state
	 */
	public abstract NamedState<?> makeState();
	
}
