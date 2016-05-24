/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Data structure for a (possibly) nested array sort.
 * In the array theory of SMT-LIB the Array sort has only two parameters one
 * for the index and one for the value.
 * We model multidimensional arrays by nesting arrays. E.g. an array with two
 * integer indices and real values has the following Sort. 
 * (Array Int -> (Array Int -> Real))
 * 
 * This is data structure is a wrapper for such a nested array sort which
 * allows you to directly access the sort of the array values and, the sort of
 * the indices.
 * This data structure allows also multidimensional arrays of dimension 0. In
 * this case, mIndex is empty.
 * @author Matthias Heizmann
 */

public class MultiDimensionalSort {
	private final ArrayList<Sort> mIndexSorts = new ArrayList<Sort>();
	private final Sort mArrayValueSort;
	
	public MultiDimensionalSort(Sort sort) {
		while (sort.isArraySort()) {
			Sort[] arg = sort.getArguments();
			assert arg.length == 2;
			mIndexSorts.add(arg[0]);
			sort = arg[1];
		}
		mArrayValueSort = sort;
	}

	public ArrayList<Sort> getIndexSorts() {
		return mIndexSorts;
	}

	public Sort getArrayValueSort() {
		return mArrayValueSort;
	}
	
	public int getDimension() {
		return mIndexSorts.size();
	}
	
	/**
	 * Given an multidimensional innerArray that can be accessed via a
	 * (partial) index form an outerArray, check if the dimensions are
	 * consistent.
	 */
	public static boolean areDimensionsConsistent(Term outerArray, 
			ArrayIndex index, Term innerArray) {
		int dimensionInnerArray = (new MultiDimensionalSort(
				innerArray.getSort())).getDimension();
		int dimensionOuterArray = (new MultiDimensionalSort(
				outerArray.getSort())).getDimension();
		return (index.size() == dimensionOuterArray - dimensionInnerArray);
	}
}
