/*
 * Copyright (C) 2013-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 * 
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission 
 * to convey the resulting work.
 */
package pea_to_boogie.generator;

import java.util.ArrayList;
import java.util.List;

public class Permutation {
    /**
     * Creates the list of all tuples in the cross product of the input arrays.
     * The tuples are integer arrays of the same length as the number of 
     * input arrays.  Every value in the resulting tuple is taken from the
     * corresponding entry in the input array. 
     * Example:  <code>crossProduct([ [1,2,3], [4,5], [6])</code> returns the list
     * <pre>[ [1,4,6], [1,5,6], [2,4,6], [2,5,6], [3,4,6], [3,5,6] ]</pre>
     *
     * @param input The input array.
     * @return the list of all tuples.
     */
    public  List<int[]> crossProduct(int[][] input) {
    	final List<int[]> result = new ArrayList<int[]>();
    	crossProductHelper(result, input, new int[input.length], 0);
    	return result;
    }
    
    /**
     * Helper function to create the cross product.  It recursively
     * fills the output array until all entries are filled and then 
     * adds it to the result list.
     * @param result the list where all tuples are added to.
     * @param input The input array, see crossProduct.
     * @param output the partially built tuple
     * @param offset the number of elements that are set in the output array.
     */
    private void crossProductHelper(List<int[]> result, 
    		int[][] input, int[] output, int offset)
    {
    	if (offset == output.length) {
    		result.add(output.clone());
    	} else {
    		for (final int v : input[offset]) {
    			output[offset] = v;
    			crossProductHelper(result, input, output, offset+1);
    		}
    	}
    }
    
    /**
     * Creates the list of all subarrays of myList of length combinationNum
     * The elements in these subarrays occur in the same order as in myList.
     * There are myList.length over combinationNum (binomial coefficient) entries
     * in the result list.
     * Example:  <code>permutation([1,2,3,4], 3)</code> returns the list
     * <pre>[ [1,2,3], [1,2,4], [1,3,4], [2,3,4] ]</pre>
     *
     * @param input The input array.
     * @param combinationNum  The number of elements in the subarrays.
     * @return the list of all subarrays.
     */
    public List<int[]> subArrays(int[] input, int combinationNum) {
    	assert(combinationNum <= input.length);
    	final List<int[]> result = new ArrayList<int[]>();
    	sublistHelper(result, input, new int[combinationNum], 0, 0);
    	return result;
    }

    /**
     * Helper function to create the list of sublists.  It recursively
     * fills the output array until all entries are filled and then 
     * adds it to the result list.
     * @param result the list where all subarrays are added to.
     * @param input The input array of which subarrays are created.
     * @param output The partially built subarray.
     * @param inputOffset The index to the first element in input array
     *                    that can be added to the output array.
     * @param outputOffset The number of elements written to the output
     *        array. This is also the index to the next element that 
     *        needs to be filled.
     */
    private void sublistHelper(List<int[]> result, int[] input, int[] output, 
    		                  int offsetInput, int offsetOutput) {
    	if (offsetOutput == output.length) {
			result.add(output.clone());
		} else {
    		final int todo = output.length - offsetOutput;
    		for (int i = offsetInput; i <= input.length - todo; i++) {
    			output[offsetOutput] = input[i];
    			sublistHelper(result, input, output, i+1, offsetOutput+1);
    		}
    	}
    }
}
