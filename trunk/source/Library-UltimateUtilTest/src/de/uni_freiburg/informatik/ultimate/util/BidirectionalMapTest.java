/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Util Library.
 * 
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Util Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.function.Consumer;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;

/**
 * Some basic tests for {@link BidirectionalMap}.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class BidirectionalMapTest {
	
	@Test
	public void testContainsValue() {
		final BidirectionalMap<String, Integer> m = new BidirectionalMap<>();
		m.put("a", 1);
		m.put("b", 2);
		assertTrue(m.containsValue(1));
		assertTrue(m.containsValue(2));
		assertFalse(m.containsValue(3));
	}
	
	@Test
	public void testClear() {
		final BidirectionalMap<String, Integer> m = new BidirectionalMap<>();
		m.put("a", 1);
		m.put("b", 2);
		m.clear();
		final Map<String, Integer> empty = new HashMap<>();
		assertEquals(empty, m);
		assertEquals(empty, m.inverse());
	}

	@Test
	public void testInverse() {
		final BidirectionalMap<String, Integer> m = new BidirectionalMap<>();
		m.put("a", 1);
		m.put("b", 2);
		m.put("c", 3);
		assertEquals(m, m.inverse().inverse());
		assertEquals(m.inverse(), m.inverse().inverse().inverse());
		assertNotEquals(m, m.inverse());
	}
	
	@Test
	public void testPut() {
		final BidirectionalMap<String, Integer> m = new BidirectionalMap<>();
		m.put("a", 1);
		m.inverse().put(2, "b");
		m.put("c", 3);
		final Map<String, Integer> expected = new HashMap<>();
		expected.put("a", 1);
		expected.put("b", 2);
		expected.put("c", 3);
		final Map<Integer, String> expectedInverse = new HashMap<>();
		expectedInverse.put(1, "a");
		expectedInverse.put(2, "b");
		expectedInverse.put(3, "c");
		assertEquals(expected, m);
		assertEquals(expectedInverse, m.inverse());
	}
	
	@Test
	public void testPutExisiting() {
		final BidirectionalMap<String, Integer> m = new BidirectionalMap<>();
		m.put("a", 1);
		final Map<String, Integer> expected = new HashMap<>();
		expected.put("a", 1);
		final Map<Integer, String> expectedInverse = new HashMap<>();
		expectedInverse.put(1, "a");

		m.put("a", 1);
		assertEquals(expected, m);
		assertEquals(expectedInverse, m.inverse());

		m.inverse().put(1, "a");
		assertEquals(expected, m);
		assertEquals(expectedInverse, m.inverse());
	}
	
	@Test
	public void testReplace() {
		final BidirectionalMap<String, Integer> m = new BidirectionalMap<>();
		m.put("a", 1);
		m.put("b", 2);
		m.put("c", 1); // replaces (a, 1)
		m.inverse().put(2, "d"); // replaces (b, 2)
		final Map<String, Integer> expected = new HashMap<>();
		expected.put("d", 2);
		expected.put("c", 1);
		final Map<Integer, String> expectedInverse = new HashMap<>();
		expectedInverse.put(2, "d");
		expectedInverse.put(1, "c");
		assertEquals(expected, m);
		assertEquals(expectedInverse, m.inverse());
	}

	@Test
	public void testRemoveKeyValue() {
		final BidirectionalMap<Integer, Integer> m = new BidirectionalMap<>();
		m.put(1, 4);
		m.put(2, 3);
		m.put(3, 2);
		m.put(4, 1);
		m.remove(1);
		m.inverse().remove(3);
		final Map<Integer, Integer> expected = new HashMap<>();
		expected.put(3, 2);
		expected.put(4, 1);
		final Map<Integer, Integer> expectedInverse = new HashMap<>();
		expectedInverse.put(2, 3);
		expectedInverse.put(1, 4);
		assertEquals(expected, m);
		assertEquals(expectedInverse, m.inverse());
	}
	
	@Test
	public void testRemove() {
		testGenericRemoveB2(m -> m.remove("b"));
	}
	
	@Test
	public void testInverseRemove() {
		testGenericRemoveB2(m -> m.inverse().remove(2));
	}
	
	@Test
	public void testKeySetRemove() {
		testUnsupportedRemoveB2(m -> m.keySet().remove("b"));
	}
	
	@Test
	public void testValuesRemove() {
		testUnsupportedRemoveB2(m -> m.values().remove(2));
	}
	
	@Test
	public void testEntrySetIteratorRemove() {
		testUnsupportedRemoveB2(m -> {
			final Iterator<Map.Entry<String, Integer>> i = m.entrySet().iterator();
			while (i.hasNext()) {
				if (i.next().getKey().equals("b")) {
					i.remove();
				}
			}
		});
	}
	
	private void testUnsupportedRemoveB2(Consumer<BidirectionalMap<String, Integer>> removeOperation) {
		// both are accepted: correct remove and unsupported operation
		try {
			testGenericRemoveB2(removeOperation);
		} catch(final UnsupportedOperationException uoe) {
			// nothing to do
		}
	}
	
	private void testGenericRemoveB2(Consumer<BidirectionalMap<String, Integer>> removeOperation) {
		final BidirectionalMap<String, Integer> m = new BidirectionalMap<>();
		m.put("a", 1);
		m.put("b", 2);
		m.put("c", 3);
		removeOperation.accept(m);
		final Map<String, Integer> expected = new HashMap<>();
		expected.put("a", 1);
		expected.put("c", 3);
		final Map<Integer, String> expectedInverse = new HashMap<>();
		expectedInverse.put(1, "a");
		expectedInverse.put(3, "c");
		assertEquals(expected, m);
		assertEquals(expectedInverse, m.inverse());
	}
	
	@Test
	public void testPutAll() {
		final BidirectionalMap<String, Integer> m = new BidirectionalMap<>();
		m.put("a", 1);
		m.put("b", 2);
		m.put("c", 3);
		final Map<String, Integer> n = new HashMap<>();
		n.put("c", 4); // replaces (c, 3)
		n.put("d", 5);
		n.put("e", 1); // replaces (a, 1)
		m.putAll(n);
		final Map<String, Integer> expected = new HashMap<>();
		expected.put("e", 1);
		expected.put("b", 2);
		expected.put("c", 4);
		expected.put("d", 5);
		final Map<Integer, String> expectedInverse = new HashMap<>();
		expectedInverse.put(1, "e");
		expectedInverse.put(2, "b");
		expectedInverse.put(4, "c");
		expectedInverse.put(5, "d");
		assertEquals(expected, m);
		assertEquals(expectedInverse, m.inverse());
	}
	
	@Test
	public void testPutSelf() {
		final BidirectionalMap<String, Integer> m = new BidirectionalMap<>();
		m.put("a", 1);
		m.put("b", 2);
		m.put("c", 3);
		final BidirectionalMap<String, Integer> mCopy = new BidirectionalMap<>(m);
		m.putAll(mCopy);
		assertEquals(mCopy, m);
		assertEquals(mCopy.inverse(), m.inverse());
	}
	
	// TODO
//	@Test
//	public void testValues() {
//		BidirectionalMap<String, Integer> m = new BidirectionalMap<>();
//		m.put("a", 1);
//		m.put("b", 2);
//		m.put("c", 3);
//	
//		// test values() equals
//
//		// test unmodifiable
//	}
	
	// TODO
//	@Test
//	public void testKeySet() {
//		BidirectionalMap<String, Integer> m = new BidirectionalMap<>();
//		m.put("a", 1);
//		m.put("b", 2);
//		m.put("c", 3);
//	
//		// test keySet() equals
//	
//		// test unmodifiable
//	}

	// Known bug, mentioned in documentation
//	@Test
//	public void testEntrySet() {
//		BidirectionalMap<String, Integer> m = new BidirectionalMap<>();
//		m.put("a", 1);
//		m.entrySet().iterator().next().setValue(2);
//		
//		BidirectionalMap<Integer, String> mInverseExpected = new BidirectionalMap<>();
//		mInverseExpected.put(2, "a");
//		
//		assertEquals(mInverseExpected, m.inverse());
//	}
}
