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
package de.uni_muenster.cs.sev.lethal.states;


/**
 * Implements a {@link State} having a name. <br>
 * Note that the name must not be changed after creation of a NamedState, not even indirectly!
 * 
 * @param <N> Type of the Name
 * 
 * @author Dorothea, Irene, Martin
 */
public class NamedState<N> implements State{

	/**
	 * The name of the state. 
	 */
	private N name;


	/**
	 * The hash code of the named state. <br> 
	 * It is calculated from the name and can be reused,
	 * since the name is never changed after creation.
	 */
	private int hashcode;


	/**
	 * Constructs a new NamedState out of a given name.
	 * 
	 * @param newname the name which the state should get 
	 */
	public NamedState(N newname){
		this.name = newname;
		this.hashcode = 31 + ((name == null) ? 0 : name.hashCode());
	}


	/**
	 * Returns the name of the state.
	 * 
	 * @return the name of this state
	 */
	public N getName(){
		return this.name;
	}


	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString(){
		return this.name.toString();
	}


	/**
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		return this.hashcode;
	}


	/**
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		NamedState<?> other = (NamedState<?>) obj;
		if (this.hashcode != other.hashcode)
			return false;
		if (this.name == null) {
			if (other.name != null)
				return false;
		} else if (!this.name.equals(other.name))
			return false;
		return true;
	}

}
