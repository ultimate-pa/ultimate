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
package de.uni_muenster.cs.sev.lethal.utils;

import java.util.Set;

/**
 * Represents a mapping between pairs (u,v) in UxV and a value type W.<br>
 * The elements of U and V are also called 'indices'.
 * 
 * @param <U> type of the row indices
 * @param <V> type of the column indices
 * @param <W> type of the values in the cells
 * 
 * @author Martin
 */
public interface TableInterface<U, V, W> {

	/**
	 * Sets the value at (u,v).
	 * @param u row index
	 * @param v column index
	 * @param w value at (u,v)
	 */
	public void setEntry(U u, V v, W w);

	/**
	 * Retrieves the value at (u,v).
	 * @param u row index
	 * @param v column index
	 * @return value at (u,v)
	 */
	public W getEntry(U u, V v);

	/**
	 * Returns whether there is a value in cell at position (u,v).
	 * @param u row index
	 * @param v column index
	 * @return true if cell at position (u,v) contains a value, false otherwise
	 */
	public boolean hasEntry(U u, V v);

	/**
	 * Returns all column indices col, where value(row,col).equals(val).
	 * @param row given row index
	 * @param val given value
	 * @return all column indices col, where value(row,col).equals(val)
	 */
	public Set<V> getColumnsWithValue(U row, W val);

}
