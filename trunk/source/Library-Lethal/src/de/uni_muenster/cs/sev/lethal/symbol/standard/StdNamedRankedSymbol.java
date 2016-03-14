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

import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;

/**
 * Standard implementation of {@link RankedSymbol ranked symbols} with names.
 * 
 * @param <N> type of name
 * 
 * @see de.uni_muenster.cs.sev.lethal.symbol.common.NamedSymbol
 * @see RankedSymbol
 * 
 * @author Anton, Dorothea, Irene, Maria, Martin, Sezar
 */
public class StdNamedRankedSymbol<N> extends AbstractNamedSymbol<N> implements RankedSymbol {

	/**
	 * The arity of this symbol.
	 */
	private int arity;


	/**
	 * Constructs a new named and ranked symbol with name and arity as specified.
	 * 
	 * @param name name of the new symbol
	 * @param arity arity of the new symbol
	 */
	public StdNamedRankedSymbol(N name, int arity) {
		super(name);
		this.arity = arity;
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol#getArity()
	 */
	@Override
	public int getArity() {
		return arity;
	}


	/**
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + this.arity;
		return result;
	}


	/**
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (!super.equals(obj))
			return false;
		if (getClass() != obj.getClass())
			return false;
		StdNamedRankedSymbol<?> other = (StdNamedRankedSymbol<?>) obj;
		if (this.arity != other.arity)
			return false;
		return true;
	}
}
