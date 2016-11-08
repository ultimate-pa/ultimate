/*
 * Copyright (C) 2015 Carl Kuesters
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.alternating;

public final class BitUtil {
	private static final long[] MASKS_SINGLE_BIT = new long[64];
	
	static {
		for (int i = 0; i < MASKS_SINGLE_BIT.length; i++) {
			MASKS_SINGLE_BIT[i] = ((long) 1) << i;
		}
	}
	
	private BitUtil() {
		// utility class, do not instantiate
	}
	
	public static long setBit(final long bitVector, final int bitIndex, final boolean value) {
		if (value) {
			return setBit(bitVector, bitIndex);
		}
		return unsetBit(bitVector, bitIndex);
	}
	
	public static long setBit(final long bitVector, final int bitIndex) {
		return bitVector | MASKS_SINGLE_BIT[bitIndex];
	}
	
	public static long unsetBit(final long bitVector, final int bitIndex) {
		return bitVector & (~MASKS_SINGLE_BIT[bitIndex]);
	}
	
	public static int getNextSetBit(final long bitVector, final int offset) {
		for (int i = offset; i < 64; i++) {
			if (getBit(bitVector, i)) {
				return i;
			}
		}
		return -1;
	}
	
	public static boolean getBit(final long bitVector, final int bitIndex) {
		return (bitVector & MASKS_SINGLE_BIT[bitIndex]) != 0;
	}
	
	public static String getText(long bitVector) {
		final StringBuilder text = new StringBuilder();
		for (int i = 0; i < 64; i++) {
			final long currentBit = bitVector & 1;
			text.append((currentBit == 1) ? 1 : 0);
			bitVector >>>= 1;
		}
		return text.toString();
	}
}
