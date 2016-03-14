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
package de.uni_muenster.cs.sev.lethal.symbol.standard;

import de.uni_muenster.cs.sev.lethal.symbol.common.NamedSymbol;

/**
 * Standard implementation of symbols with a name. <br> 
 * A name is some additional information which characterizes the symbol, 
 * i.e. two named symbols are equal if and only if their names are equal.<br>
 * Do not change the name after initalizing!
 *
 * @param <N> type of name
 * 
 * @author Anton, Dorothea, Irene, Maria, Martin, Sezar
 */
public abstract class AbstractNamedSymbol<N> implements NamedSymbol<N> {

	/**
	 * The name of the symbol.
	 */
	private final N name;


	/**
	 * Pre-caluclated hashcode of the symbol.
	 */
	private final int hashCode;


	/**
	 * Constructs a new named symbol out of the given name.
	 *
	 * @param name name of the new symbol
	 */
	public AbstractNamedSymbol(N name) {
		this.name = name;
		hashCode = calculateHashCode();
	}


	/**
	 * Calculates the hash code.
	 * 
	 * @return newly calculated hash code
	 */
	private int calculateHashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
		+ ((this.name == null) ? 0 : this.name.hashCode());
		return result;
	}


	/**
	 * @return name of the symbol
	 */
	@Override
	public N getName() {
		return name;
	}


	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return name.toString();
	}


	/**
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		return hashCode;
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
		AbstractNamedSymbol<?> other = (AbstractNamedSymbol<?>) obj;
		if (this.name == null) {
			if (other.name != null)
				return false;
		} else if (!this.name.equals(other.name))
			return false;
		return true;
	}
}
