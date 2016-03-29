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
 * Stores different interfaces that represent different types of symbols.
 */
package de.uni_muenster.cs.sev.lethal.symbol.common;

/**
 * Represents a symbol which can be of two different types, but not both at the
 * same time.<br>
 * <ul>
 * <li>The first kind, which is called <em>inner</em> type, is a kind of symbol
 * which can occur on some inner node (which has subtrees), but not necessarily,
 * that means it can also occur as a leaf.
 * <li>The second kind, which is called <em>leaf</em> type, is a kind of symbol
 * which occurs necessarily as a leaf, that means it never occurs on any inner
 * node.
 * </ul>
 * Examples for use of this symbol type include:<br>
 * <ul>
 * <li>Grammar trees, where the inner type is function symbol and the leaf type
 * is non-terminal.
 * <li>Variable trees, where the inner type is function symbol and the leaf type
 * is variable.
 * <li>Configuration trees, where the inner type is function symbol and the leaf
 * type is state.
 * </ul>
 * Invariants: <br>
 * <ul>
 * <li>Either isInnerType() or isLeafType() returns always true, but not both.</li>
 * <li>If isLeafType() returns true, then asLeafSymbol() does not return null.</li>
 * <li>If isInnerType() returns true, then asInnerSymbol() does not return null.
 * </li>
 * </ul>
 * 
 * <em> Note: </em> Inner symbols can occur as leaves, but are nevertheless
 * inner symbols.
 * 
 * @param <I> inner symbol type
 * @param <L> leaf symbol type
 * 
 * @author Martin, Dorothea, Irene
 * 
 */
public interface BiSymbol<I extends Symbol, L> extends Symbol {

	/**
	 * Returns whether an inner type is represented.
	 * 
	 * @return true if an inner type is represented, false otherwise.
	 */
	boolean isInnerType();

	/**
	 * Returns whether a leaf type is represented.
	 * 
	 * @return true if a leaf type is represented, false otherwise.
	 */
	boolean isLeafType();

	/**
	 * Returns the represented inner symbol, if an inner symbol is represented.
	 * 
	 * @return the represented inner symbol, if an inner symbol is represented.
	 */
	I asInnerSymbol();

	/**
	 * Returns the represented leaf symbol, if a leaf symbol is represented.
	 * 
	 * @return the represented leaf symbol, if a leaf symbol is represented.
	 */
	L asLeafSymbol();
}