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
 * Represents a mapping between pairs (u,v) in UxV and a value type W.
 * The mapping between pairs (u,v) in UxV and values
 * of type W as achieved by mapping u and v to certain array indices
 * and by identifying objects of type W with integer values. <br>
 * The set of possible values can be dynamically extended.
 * 
 * @param <U> type of the row indices
 * @param <V> type of the column indices
 * @param <W> type of the possible values
 * 
 * @author Martin
 */
public class Table<U,V,W> implements TableInterface<U,V,W> {

	/** Translates the row indices into numbers for accessing the actual data. */
	private Map<U,Integer> rowToIndex = new HashMap<U,Integer>();


	/** Translates the column indices into numbers for accessing the actual data. */
	private Map<V,Integer> colToIndex = new HashMap<V,Integer>();


	/** Inverse mapping of colIndex, which maps the numbers to the corresponding column indices. */
	private Map<Integer,V> indexToCol = new HashMap<Integer,V>();


	/** Maps the possible values to numbers. */
	private Map<W,Integer> valuesToIndex = new HashMap<W,Integer>();


	/** Inverse maping of valuesToIndex, to get back the value from its code. */
	private Map<Integer,W> indexToValues = new HashMap<Integer,W>();


	/** Highest number which can occur in the data-array. */
	private int maxValueIndex=0;


	/** The number of the rows in the table. */
	private int numRows;


	/** The number of the columns in the table. */
	private int numCols;


	/**
	 * The table itself is a two-dimensional array of integers.
	 * The mapping between pairs (u,v) in UxV and values
	 * of type W is achieved by mapping u and v to certain array indices
	 * and by identifying objects of type W with integer values. 
	 */
	private int[][] data;


	/** Code for no empty cells. */
	private static int NO_VALUE = -1;


	/**
	 * Initializes the table with given row set and column set.
	 * 
	 * @param rows rows of the new table
	 * @param cols columns of the new table
	 */
	public Table(Set<U> rows, Set<V> cols) {
		numRows=0;
		for (U u: rows) {
			rowToIndex.put(u,numRows);
			numRows++;
		}

		numCols=0;
		for (V v: cols) {
			colToIndex.put(v, numCols);
			indexToCol.put(numCols, v);
			numCols++;
		}

		data = new int[numRows][numCols];
		for (int i=0; i<numRows; i++)
			for (int j=0; j<numCols; j++)
				data[i][j]=NO_VALUE;


	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.utils.TableInterface#getColumnsWithValue(java.lang.Object, java.lang.Object)
	 */
	@Override
	public Set<V> getColumnsWithValue(U row, W val) {
		int i0 = rowToIndex.get(row);
		int indexOfValue = valuesToIndex.get(val);
		Set<V> ret = new HashSet<V>();
		for (int j=0; j<numCols; j++) {
			if (data[i0][j]==indexOfValue)
				ret.add(indexToCol.get(j));
		}
		return ret;
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.utils.TableInterface#getEntry(java.lang.Object, java.lang.Object)
	 */
	@Override
	public W getEntry(U u, V v) {
		int row = rowToIndex.get(u);
		int col = colToIndex.get(v);
		int datum = data[row][col];
		return indexToValues.get(datum);
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.utils.TableInterface#hasEntry(java.lang.Object, java.lang.Object)
	 */
	@Override
	public boolean hasEntry(U u, V v) {
		int row = rowToIndex.get(u);
		int col = colToIndex.get(v);
		return data[row][col] != NO_VALUE;
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.utils.TableInterface#setEntry(java.lang.Object, java.lang.Object, java.lang.Object)
	 */
	@Override
	public void setEntry(U u, V v, W w) {
		int row = rowToIndex.get(u);
		int col = colToIndex.get(v);
		int indexOfValue;
		if (valuesToIndex.containsKey(w))
			indexOfValue = valuesToIndex.get(w);
		else {
			valuesToIndex.put(w, maxValueIndex);
			indexToValues.put(maxValueIndex,w);
			indexOfValue = maxValueIndex;
			maxValueIndex++;
		}
		data[row][col] = indexOfValue;
	}
}
