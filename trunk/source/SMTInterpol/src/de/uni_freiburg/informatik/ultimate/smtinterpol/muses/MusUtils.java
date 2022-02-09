/*
 * Copyright (C) 2020 Leonard Fichtner
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Random;

/**
 * Contains methods that are used all over the package "muses".
 *
 * @author LeonardFichtner
 *
 */
public class MusUtils {

	/**
	 * Check whether set1 contains set2.
	 */
	public static boolean contains(final BitSet set1, final BitSet set2) {
		final BitSet set2Clone = (BitSet) set2.clone();
		set2Clone.andNot(set1);
		return set2Clone.isEmpty();
	}

	/**
	 * Takes in a BitSet and returns an Array with the indices of the set Bits, but randomly permuted (pseudo-randomly,
	 * this method always uses the same seed).
	 */
	public static ArrayList<Integer> randomPermutation(final BitSet toBePermutated, final Random rnd) {
		final ArrayList<Integer> toShuffle = new ArrayList<>();
		for (int i = toBePermutated.nextSetBit(0); i >= 0; i = toBePermutated.nextSetBit(i + 1)) {
			toShuffle.add(i);
		}
		java.util.Collections.shuffle(toShuffle, rnd);
		return toShuffle;
	}

	/**
	 * Pops the last element of an arraylist.
	 */
	public static int pop(final ArrayList<Integer> list) {
		final int lastElem = list.get(list.size() - 1);
		list.remove(list.size() - 1);
		return lastElem;
	}

}
