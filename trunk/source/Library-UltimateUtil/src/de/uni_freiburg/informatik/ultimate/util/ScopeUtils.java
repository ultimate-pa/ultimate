/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.util.Arrays;

/**
 * This class collects some constants and default functions to assist scoped
 * container implementations.
 * @author Juergen Christ
 */
public final class ScopeUtils {
	private ScopeUtils() {
		// Hide constructor
	}
	/**
	 * Number of scopes initially reserved.
	 */
	public static final int NUM_INITIAL_SCOPES = 5;
	/**
	 * The growth function for internal scope arrays.  The arrays grow by a
	 * constant amount {@link #NUM_ADDITIONAL_SCOPES NUM_ADDITIONAL_SCOPES}.
	 * @param curarray Current internal scope array.
	 * @return New internal scope array
	 */
	public static final <E> E[] grow(E[] curarray) {
		return Arrays.copyOf(curarray, curarray.length * 2);
	}
	/**
	 * The growth function for internal integer scope arrays.  The arrays grow 
	 * by a constant amount
	 * {@link #NUM_ADDITIONAL_SCOPES NUM_ADDITIONAL_SCOPES}.
	 * @param curarray Current internal scope array.
	 * @return New internal scope array
	 */
	public static final int[] grow(int[] curarray) {
		return Arrays.copyOf(curarray, curarray.length * 2);
	}
	/**
	 * Should the internal scope array be shrunk?
	 * @param <E>		Type stored in the internal scope array.
	 * @param array		The internal scope array.
	 * @return <code>true</code> if and only if the array should be shrunk.
	 */
	public static final <E> boolean shouldShrink(E[] array) {
		return array.length > NUM_INITIAL_SCOPES
				&& array[array.length >> 2] == null;
	}
	/**
	 * Should the internal integer scope array be shrunk?
	 * @param used	Number of slots used in the scope array.
	 * @param size The size of the array.
	 * @return <code>true</code> if and only if the array should be shrunk.
	 */
	public static final boolean shouldShrink(int used, int size) {
		return size > NUM_INITIAL_SCOPES && used < (size >> 2);
	}
	/**
	 * Shrink the internal scope array.
	 * @param <E>		Type stored in the internal scope array.
	 * @param curarray	Internal scope array.
	 * @return Smaller array that should be used as internal scope array.
	 */
	public static final <E> E[] shrink(E[] curarray) {
		return Arrays.copyOf(curarray, curarray.length >> 1);
	}
	/**
	 * Shrink the internal integer scope array.
	 * @param curarray	Internal scope array.
	 * @return Smaller array that should be used as internal scope array.
	 */
	public static final int[] shrink(int[] curarray) {
		return Arrays.copyOf(curarray, curarray.length >> 1);
	}

}
