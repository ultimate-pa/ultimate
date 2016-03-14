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
/**
 * 
 */
package de.uni_muenster.cs.sev.lethal.symbol.special;

import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;


/**
 * Special binary symbol for constructing arbitrarily long lists. <br>
 * Implemented as singleton.
 * 
 * @author Anton, Maria
 */
public final class Cons implements RankedSymbol{

	/** Only instance of this class. */
	private static final Cons CONS = new Cons();


	/** Private constructor, so that an instance of this class cannot be created from outside. */
	private Cons() {
	}


	/**
	 * Returns the only instance of this class.
	 * 
	 * @return the only instance of this class
	 */
	public static Cons getCons() {
		return CONS;
	}


	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "#cons";
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol#getArity()
	 */
	@Override
	public int getArity() {
		return 2;
	}
}
