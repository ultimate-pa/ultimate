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
package de.uni_muenster.cs.sev.lethal.tree.common;

import java.util.List;

import de.uni_muenster.cs.sev.lethal.symbol.common.Symbol;

/**
 * Common interface for all tree and hedge structures.
 * 
 * @author Anton, Dorothea, Irene, Maria, Martin, Philipp, Sezar
 *
 * @param <S> tree node symbol type
 */
public interface Tree<S extends Symbol> {

	/**
	 * Returns the list of the subtrees of this tree.
	 * 
	 * @return the list of the subtrees of this tree
	 */
	public List<? extends Tree<S>> getSubTrees();

	/**
	 * Returns the root symbol of this tree.
	 * 
	 * @return the root symbol of this tree
	 */
	public S getSymbol();

	/**
	 * Returns the common super class of the symbols in this tree. 
	 * 
	 * @return the common super class of the symbols in this tree
	 */
	public Class<? extends Symbol> getSymbolClass();
}
