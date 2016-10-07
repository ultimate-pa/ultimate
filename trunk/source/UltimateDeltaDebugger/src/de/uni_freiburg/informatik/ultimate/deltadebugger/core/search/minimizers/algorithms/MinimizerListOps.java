package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Provides basic list operators used by the minimizer implementations.
 */
public class MinimizerListOps {
	
	private MinimizerListOps() {
	}
	
	/**
	 * Allocate a new list of the requested capacity.
	 * 
	 * @param capacity
	 * @return list
	 */
	public static <E> List<E> newList(int capacity) {
		return new ArrayList<>(capacity);
	}
	
	/**
	 * Returns the sublist between the specified
	 * <tt>fromIndex</tt>, inclusive, and <tt>toIndex</tt>, exclusive.
	 * 
	 * @param source source list
	 * @param fromIndex low endpoint (inclusive) of the subsequence
	 * @param toIndex high endpoint (exclusive) of the subsequence
	 * @return a list containing the subsequence of the source list in the specified range
	 */
	public static <E> List<E> subList(List<E> source, int fromIndex, int toIndex) {
		return source.subList(fromIndex, toIndex);
	}

	/**
	 * Returns the complement of the sublist between the specified
	 * <tt>fromIndex</tt>, inclusive, and <tt>toIndex</tt>, exclusive.
	 * 
	 * @param source source list
	 * @param fromIndex low endpoint (inclusive) of the subsequence to remove
	 * @param toIndex high endpoint (exclusive) of the subsequence to remove
	 * @return a list containing the subsequence of the source list not in the specified range
	 */
	public static <E> List<E> subListComplement(List<E> source, int fromIndex, int toIndex) {
		final int size = source.size();
		if (fromIndex < 0 || toIndex > size || fromIndex > toIndex) {
			throw new IndexOutOfBoundsException();
		}
		// Only create a copy if necessary
		if (fromIndex == toIndex) {
			return source;
		}
		if (fromIndex == 0) {
			if (toIndex == size) {
				return Collections.emptyList();
			}
			return subList(source, toIndex, size);
		}
		if (toIndex == size) {
			return subList(source, 0, fromIndex);
		}
		final List<E> complement = newList(source.size() - (toIndex - fromIndex));
		complement.addAll(source.subList(0, fromIndex));
		complement.addAll(source.subList(toIndex, size));
		return complement;
	}
}