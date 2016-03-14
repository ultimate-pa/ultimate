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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * Represents a mapping f between pairs (u,v) in UxV and boolean values. <br>
 * The mapping is symmetric, that means, f(u,v) = f(v,u) for all (u,v), and
 * reflexive, that means, f(u,u) is always true.<br>
 * Knowing that there are only three possible values (true, false and null for
 * no value) makes the encoding of the values as integers obsolete and therefore
 * the operations a little more efficient than in {@link Table}.
 * 
 * @param <U> type of the row and column indices
 * 
 * @see TableInterface
 * @see Table
 * 
 * @author Martin
 */
public class SymmetricBoolTable<U> implements TableInterface<U,U,Boolean> {


	/** Translates the row indices into numbers for accessing the actual data. */
	private Map<U,Integer> rowColToIndex = new HashMap<U,Integer>();


	/** Inverse mapping of colIndex, which maps the numbers to the corresponding column indices. */
	private Map<Integer,U> indexToRowCol = new HashMap<Integer,U>();


	/**
	 * The number of the rows in the table.
	 */
	private int numRowCols;


	/**
	 * The table itself as two-dimensional array of Boolean objects
	 * The mapping between pairs (u,v) in UxV and values
	 * of type W is archieved by mapping u and v to certain array indices. 
	 */
	private Boolean[][] data;


	/**
	 * The set of cells of this table. Note, that if (u,v) is contained
	 * and u!=v, then (v,u) is not contained.
	 */
	private Set<Pair<U,U>> cells = null;


	/**
	 * Initializes the table with given row and column set.
	 * 
	 * @param rowsCols row and column set of the new table
	 */
	public SymmetricBoolTable(Set<U> rowsCols) {
		numRowCols=0;
		for (U u: rowsCols) {
			rowColToIndex.put(u,numRowCols);
			indexToRowCol.put(numRowCols, u);
			numRowCols++;
		}

		data = new Boolean[numRowCols][numRowCols];
		for (int i=0; i<numRowCols; i++)
			for (int j=i+1; j<numRowCols; j++)
				data[i][j]=null;
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.utils.TableInterface#getColumnsWithValue(java.lang.Object, java.lang.Object)
	 */
	@Override
	public Set<U> getColumnsWithValue(U row, Boolean val) {
		int i0 = rowColToIndex.get(row);
		Set<U> ret = new HashSet<U>();
		for (int j=0; j<i0; j++)
			if (data[j][i0].equals(val))
				ret.add(indexToRowCol.get(j));

		ret.add(row);

		for (int j=i0+1; j<numRowCols; j++) {
			if (data[i0][j].equals(val))
				ret.add(indexToRowCol.get(j));
		}
		return ret;
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.utils.TableInterface#getEntry(java.lang.Object, java.lang.Object)
	 */
	@Override
	public Boolean getEntry(U u, U v) {
		if (u.equals(v))
			return true;

		int row = rowColToIndex.get(u);
		int col = rowColToIndex.get(v);
		if (row<col)
			return data[row][col];
		else
			return data[col][row];
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.utils.TableInterface#hasEntry(java.lang.Object, java.lang.Object)
	 */
	@Override
	public boolean hasEntry(U u, U v) {
		int row = rowColToIndex.get(u);
		int col = rowColToIndex.get(v);
		return data[row][col]!=null || data[col][row]!=null;
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.utils.TableInterface#setEntry(java.lang.Object, java.lang.Object, java.lang.Object)
	 */
	@Override
	public void setEntry(U u, U v, Boolean w) {
		int row = rowColToIndex.get(u);
		int col = rowColToIndex.get(v);
		if (row<col)
			data[row][col] = w;
		else
			if (col<row)
				data[col][row] = w;
	}

	/**
	 * Returns the set of cells as pairs (u,v) of the row and column objects. Because of the symmetry
	 * of the mapping, if (u,v) is contained in the returned set, (v,u) is not contained
	 * @return the set of cells as pairs (u,v) of the row and column objects
	 */
	public Set<Pair<U,U>> getCells() {
		if (this.cells==null) {
			cells = new HashSet<Pair<U,U>>();
			for (int row=0; row<numRowCols; row++)
				for (int col=row+1; col<numRowCols; col++)
					cells.add(new Pair<U,U>(indexToRowCol.get(row), indexToRowCol.get(col)));
		}

		return cells;
	}
}
