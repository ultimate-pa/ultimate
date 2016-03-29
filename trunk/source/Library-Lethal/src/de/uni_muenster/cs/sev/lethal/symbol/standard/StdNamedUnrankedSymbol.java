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

import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;

/**
 * Standard implementation of unranked symbols with names.
 *
 * @param <N> type of name
 * 
 * @see de.uni_muenster.cs.sev.lethal.symbol.common.NamedSymbol
 * @see UnrankedSymbol
 * 
 * @author Anton, Dorothea, Irene, Maria, Martin, Sezar
 * 
 */
public class StdNamedUnrankedSymbol<N> extends AbstractNamedSymbol<N> implements UnrankedSymbol {


	/**
	 * Constructs a new named and ranked symbol with name and arity as specified.
	 *
	 * @param name name of the new symbol
	 */
	public StdNamedUnrankedSymbol(N name) {
		super(name);
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.symbol.standard.AbstractNamedSymbol#toString()
	 */
	@Override
	public String toString(){
		return this.getName().toString();
	}
}
