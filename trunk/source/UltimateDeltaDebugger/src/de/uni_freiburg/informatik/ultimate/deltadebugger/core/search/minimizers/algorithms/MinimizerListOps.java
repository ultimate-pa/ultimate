/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Provides basic list operators used by the minimizer implementations.
 */
public final class MinimizerListOps {
	private MinimizerListOps() {
		// utility class
	}
	
	/**
	 * Allocate a new list of the requested capacity.
	 *
	 * @param capacity
	 *            capacity
	 * @param <E>
	 *            element type
	 * @return list
	 */
	public static <E> List<E> newList(final int capacity) {
		return new ArrayList<>(capacity);
	}
	
	/**
	 * Returns the sublist between the specified <tt>fromIndex</tt>, inclusive, and <tt>toIndex</tt>, exclusive.
	 *
	 * @param source
	 *            source list
	 * @param fromIndex
	 *            low endpoint (inclusive) of the subsequence
	 * @param toIndex
	 *            high endpoint (exclusive) of the subsequence
	 * @param <E>
	 *            element type
	 * @return a list containing the subsequence of the source list in the specified range
	 */
	public static <E> List<E> subList(final List<E> source, final int fromIndex, final int toIndex) {
		return source.subList(fromIndex, toIndex);
	}
	
	/**
	 * Returns the complement of the sublist between the specified <tt>fromIndex</tt>, inclusive, and <tt>toIndex</tt>,
	 * exclusive.
	 *
	 * @param source
	 *            source list
	 * @param fromIndex
	 *            low endpoint (inclusive) of the subsequence to remove
	 * @param toIndex
	 *            high endpoint (exclusive) of the subsequence to remove
	 * @param <E>
	 *            element type
	 * @return a list containing the subsequence of the source list not in the specified range
	 */
	public static <E> List<E> subListComplement(final List<E> source, final int fromIndex, final int toIndex) {
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
