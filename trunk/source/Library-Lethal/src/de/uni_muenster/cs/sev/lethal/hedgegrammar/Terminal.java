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
package de.uni_muenster.cs.sev.lethal.hedgegrammar;

import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;

/**
 * represents a terminal symbol needed to describe expressions for a schema
 * 
 * @author Anton, Maria
 * @param <G_Symbol> symbol type of the hedge grammar
 */
public class Terminal<G_Symbol extends UnrankedSymbol> /* extends SchemaExpression */{

	/**
	 * Symbol describing the terminal symbol
	 */
	private G_Symbol sym;

	/**
	 * constructor
	 * 
	 * @param symbol symbol describing the terminal
	 */
	public Terminal(G_Symbol symbol) {
		super();
		sym = symbol;
	}

	/**
	 * Returns the symbol describing the terminal
	 * @return the symbol describing the terminal
	 */
	public G_Symbol getSymbol() {
		return sym;
	}

	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return sym.toString();
	}
}
