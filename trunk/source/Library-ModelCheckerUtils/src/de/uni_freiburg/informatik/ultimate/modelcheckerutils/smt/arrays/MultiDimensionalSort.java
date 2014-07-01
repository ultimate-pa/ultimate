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
 * this case, m_Index is empty.
 * @author Matthias Heizmann
 */

public class MultiDimensionalSort {
	private final ArrayList<Sort> m_IndexSorts = new ArrayList<Sort>();
	private final Sort m_ArrayValueSort;
	
	public MultiDimensionalSort(Sort sort) {
		while (sort.isArraySort()) {
			Sort[] arg = sort.getArguments();
			assert arg.length == 2;
			m_IndexSorts.add(arg[0]);
			sort = arg[1];
		}
		m_ArrayValueSort = sort;
	}

	public ArrayList<Sort> getIndexSorts() {
		return m_IndexSorts;
	}

	public Sort getArrayValueSort() {
		return m_ArrayValueSort;
	}
	
	public int getDimension() {
		return m_IndexSorts.size();
	}
	
	/**
	 * Given an multidimensional innerArray that can be accessed via a
	 * (partial) index form an outerArray, check if the dimensions are
	 * consistent.
	 */
	public static boolean areDimensionsConsistent(Term outerArray, 
			Term[] index, Term innerArray) {
		int dimensionInnerArray = (new MultiDimensionalSort(
				innerArray.getSort())).getDimension();
		int dimensionOuterArray = (new MultiDimensionalSort(
				outerArray.getSort())).getDimension();
		return (index.length == dimensionOuterArray - dimensionInnerArray);
	}
}