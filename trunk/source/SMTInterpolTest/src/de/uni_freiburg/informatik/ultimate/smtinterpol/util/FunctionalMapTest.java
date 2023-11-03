/*
 * Copyright (C) 2009-2021 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Random;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class FunctionalMapTest {

	Random rng = new Random(1234567);

	@Test
	public void testRandomInsertRemoval() {
		final ArrayList<Integer> numbers = new ArrayList<>();
		final HashMap<Integer, Integer> controlMap = new HashMap<>();
		FunctionalMap<Integer, Integer> map = FunctionalMap.empty();
		for (int i = 0; i < 1000; i++) {
			Assert.assertEquals(i, map.size());
			int rndNumber = rng.nextInt(10000);
			while (map.containsKey(rndNumber)) {
				final int pos = map.get(rndNumber);
				assert numbers.get(pos) == rndNumber;
				rndNumber = rng.nextInt(10000);
			}
			map = map.insert(rndNumber, i);
			controlMap.put(rndNumber, i);
			numbers.add(rndNumber);
		}
		final FunctionalMap<Integer, Integer> copy = map;
		for (final int number : map.keySet()) {
			final int pos = map.get(number);
			Assert.assertEquals(number, (int) numbers.get(pos));
		}
		Assert.assertEquals(map.size(), 1000);
		while (numbers.size() > 0) {
			Assert.assertEquals(numbers.size(), map.size());
			final int randomPos = rng.nextInt(numbers.size());
			final int number = numbers.get(randomPos);
			final int last = numbers.remove(numbers.size() - 1);
			if (randomPos < numbers.size()) {
				numbers.set(randomPos, last);
			}
			Assert.assertTrue(map.containsKey(number));
			Assert.assertEquals((int) controlMap.get(number), (int) map.get(number));
			Assert.assertEquals((int) copy.get(number), (int) map.get(number));
			map = map.delete(number);
		}
		map = copy;
		Assert.assertTrue(map.size() == 1000);
		for (final int number : copy.keySet()) {
			map = map.delete(number);
		}
		Assert.assertTrue(map.isEmpty());
	}

	/**
	 * Test if the map can handle keys with colliding hash codes.
	 */
	@Test
	public void testBadHash() {
		final ArrayList<Integer> numbers = new ArrayList<>();
		final HashMap<Integer, Integer> controlMap = new HashMap<>();
		FunctionalMap<StupidKey, Integer> map = FunctionalMap.empty();
		for (int i = 0; i < 1000; i++) {
			Assert.assertEquals(i, map.size());
			int rndNumber = rng.nextInt(10000);
			while (map.containsKey(new StupidKey(rndNumber))) {
				final int pos = map.get(new StupidKey(rndNumber));
				assert numbers.get(pos) == rndNumber;
				rndNumber = rng.nextInt(10000);
			}
			map = map.insert(new StupidKey(rndNumber), i);
			controlMap.put(rndNumber, i);
			numbers.add(rndNumber);
		}
		for (final StupidKey number : map.keySet()) {
			final int pos = map.get(number);
			Assert.assertEquals(number.getValue(), (int) numbers.get(pos));
		}
		Assert.assertEquals(map.size(), 1000);
		while (numbers.size() > 0) {
			Assert.assertEquals(numbers.size(), map.size());
			final int randomPos = rng.nextInt(numbers.size());
			final int number = numbers.get(randomPos);
			final int last = numbers.remove(numbers.size() - 1);
			if (randomPos < numbers.size()) {
				numbers.set(randomPos, last);
			}
			Assert.assertTrue(map.containsKey(new StupidKey(number)));
			Assert.assertEquals((int) controlMap.get(number), (int) map.get(new StupidKey(number)));
			map = map.delete(new StupidKey(number));
		}
	}

	/**
	 * Test class for keys with very bad hash code.
	 */
	class StupidKey {
		final int mValue;

		public StupidKey(final int value) {
			mValue = value;
		}

		public int getValue() {
			return mValue;
		}

		/**
		 * A very bad hash code implementation to cause lots of conflicts.
		 */
		@Override
		public int hashCode() {
			return mValue & 0xff;
		}

		@Override
		public boolean equals(final Object other) {
			return other instanceof StupidKey && ((StupidKey) other).mValue == mValue;
		}

		@Override
		public String toString() {
			return String.valueOf(mValue);
		}
	}
}
