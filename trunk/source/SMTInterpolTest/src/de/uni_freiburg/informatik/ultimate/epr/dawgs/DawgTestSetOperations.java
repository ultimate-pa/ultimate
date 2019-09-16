/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.epr.dawgs;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;

/**
 * Tests for the standard set operations on dawgs.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
@RunWith(JUnit4.class)
public class DawgTestSetOperations {

	private DawgState<String, Boolean> dawg1;
	private TreeSet<Integer> signature1;
	private List<String> word_aa;
	private DawgState<String, Boolean> dawg2;
	private List<String> word_ac;
	private List<String> word_ba;
	private List<String> word_bb;
	private List<String> word_bc;
	private List<String> word_ca;
	private List<String> word_cb;
	private List<String> word_cc;
	private DawgState<String, Boolean> dawg3;
	private List<String> word_ab;
	private DawgState<String, Boolean> dawg4;
	private DawgState<String, Boolean> dawg5;
	private DawgState<String, Boolean> dawg6;
	private DawgState<String, Boolean> dawg7;
	private DawgState<String, Boolean> dawg8;
	private DawgState<String, Boolean> dawg9;
	private DawgState<String, Boolean> dawg10;
	private DawgState<String, Boolean> dawg11;
	private DawgState<String, Boolean> dawg12;
	private DawgState<String, Boolean> dawg13;
	private DawgState<String, Boolean> dawg14;
	private DawgFactory<String, Integer> dawgFactory;




	@Before
	public void setup() {
		dawgFactory = new DawgFactory<String, Integer>(EprTestHelpers.getEprTheory());
		EprTestHelpers.addConstantsWDefaultSort(dawgFactory, EprTestHelpers.constantsAbc());

		signature1 = new TreeSet<Integer>(Arrays.asList(new Integer[] { 1, 2 }));
		dawg1 = dawgFactory.createConstantDawg(signature1, Boolean.FALSE);

		word_aa = Arrays.asList(new String[] { "a", "a" });
		dawg2 = dawgFactory.createSingletonSet(signature1, word_aa);

		word_ab = Arrays.asList(new String[] { "a", "b" });
		word_ac = Arrays.asList(new String[] { "a", "c" });
		word_ba = Arrays.asList(new String[] { "b", "a" });
		word_bb = Arrays.asList(new String[] { "b", "b" });
		word_bc = Arrays.asList(new String[] { "b", "c" });
		word_ca = Arrays.asList(new String[] { "c", "a" });
		word_cb = Arrays.asList(new String[] { "c", "b" });
		word_cc = Arrays.asList(new String[] { "c", "c" });

		dawg3 = dawg2;
		dawg3 = dawgFactory.createUnion(dawg3, dawgFactory.createSingletonSet(signature1, word_ab));
		dawg3 = dawgFactory.createUnion(dawg3, dawgFactory.createSingletonSet(signature1, word_ac));
		dawg3 = dawgFactory.createUnion(dawg3, dawgFactory.createSingletonSet(signature1, word_ba));
		dawg3 = dawgFactory.createUnion(dawg3, dawgFactory.createSingletonSet(signature1, word_bb));
		dawg3 = dawgFactory.createUnion(dawg3, dawgFactory.createSingletonSet(signature1, word_bc));
		dawg3 = dawgFactory.createUnion(dawg3, dawgFactory.createSingletonSet(signature1, word_ca));
		dawg3 = dawgFactory.createUnion(dawg3, dawgFactory.createSingletonSet(signature1, word_cb));
		dawg7 = dawg3;
		dawg3 = dawgFactory.createUnion(dawg3, dawgFactory.createSingletonSet(signature1, word_cc));

		dawg4 = dawgFactory.createUnion(dawg2, dawgFactory.createSingletonSet(signature1, word_ab));
		dawg4 = dawgFactory.createUnion(dawg4, dawgFactory.createSingletonSet(signature1, word_ac));

		dawg5 = dawgFactory.createUnion(dawg4, dawgFactory.createSingletonSet(signature1, word_ba));

		dawg6 = dawgFactory.createMapped(dawg3, in -> !in);
		dawg8 = dawgFactory.createMapped(dawg7, in -> !in);

		dawg9 = dawgFactory.createConstantDawg(signature1, Boolean.FALSE);
		dawg9 = dawgFactory.createUnion(dawg9, dawgFactory.createSingletonSet(signature1, word_aa));
		dawg9 = dawgFactory.createUnion(dawg9, dawgFactory.createSingletonSet(signature1, word_ab));

		dawg10 = dawgFactory.createConstantDawg(signature1, Boolean.FALSE);
		dawg10 = dawgFactory.createUnion(dawg10, dawgFactory.createSingletonSet(signature1, word_ab));
		dawg10 = dawgFactory.createUnion(dawg10, dawgFactory.createSingletonSet(signature1, word_ac));

		dawg11 = dawgFactory.createIntersection(dawg9, dawg10);

		dawg12 = dawgFactory.createMapped(dawg11, in -> !in);
		dawg12 = dawgFactory.createUnion(dawg12, dawgFactory.createSingletonSet(signature1, word_ab));

		dawg13 = dawgFactory.createSingletonSet(signature1, word_ba);
		dawg13 = dawgFactory.createUnion(dawg13, dawgFactory.createSingletonSet(signature1, word_bb));
		dawg13 = dawgFactory.createUnion(dawg13, dawgFactory.createSingletonSet(signature1, word_bc));
		dawg13 = dawgFactory.createUnion(dawg13, dawgFactory.createSingletonSet(signature1, word_ca));
		dawg13 = dawgFactory.createUnion(dawg13, dawgFactory.createSingletonSet(signature1, word_cb));
		dawg13 = dawgFactory.createUnion(dawg13, dawgFactory.createSingletonSet(signature1, word_cc));

		dawg14 = dawgFactory.createUnion(dawg9, dawg10);
		dawg14 = dawgFactory.createUnion(dawg14, dawg13);
	}

	/**
	 * Convert a dawg to a set.
	 *
	 * @param dawg
	 *            the dawg to convert
	 * @return the resulting set.
	 */
	private <T> Set<List<T>> toSet(final DawgState<T, Boolean> dawg) {
		final Set<List<T>> set = new HashSet<>();
		for (final List<T> word : DawgFactory.getSet(dawg)) {
			set.add(word);
		}
		return set;
	}

	@Test
	public void testDawg1() {
		assertFalse(DawgFactory.getSet(dawg1).iterator().hasNext());
		assertTrue(DawgFactory.isEmpty(dawg1));
		assertFalse(DawgFactory.isUniversal(dawg1));
		assertFalse(DawgFactory.isSingleton(dawg1));
	}

	@Test
	public void testDawg2() {
		assertEquals(Collections.singleton(word_aa), toSet(dawg2));
		assertFalse(DawgFactory.isEmpty(dawg2));
		assertFalse(DawgFactory.isUniversal(dawg2));
		assertTrue(DawgFactory.isSingleton(dawg2));
		assertTrue(dawg2.getValue(word_aa));
		assertFalse(dawg2.getValue(word_ab));
	}

	@Test
	public void testDawg3() {
		assertFalse(DawgFactory.isSingleton(dawg3));
	}

	@Test
	public void testDawg4() {
		assertTrue(dawg4.getValue(word_ab));
		assertTrue(dawg4.getValue(word_ac));
		assertFalse(dawg4.getValue(word_ba));
	}

	@Test
	public void testDawg5() {
		assertTrue(dawg5.getValue(word_aa));
		assertTrue(dawg5.getValue(word_ba));
	}

	@Test
	public void testDawg6() {
		assertEquals(Collections.emptySet(), toSet(dawg6));
//		assertTrue(dawg6.isEmpty()); // not empty by new AllConstants convention!
	}

	@Test
	public void testDawg7() {
		assertFalse(DawgFactory.isEmpty(dawg7));
		assertFalse(DawgFactory.isUniversal(dawg7));
		assertFalse(DawgFactory.isSingleton(dawg7));
		assertFalse(dawg7.getValue(word_cc));
	}

	@Test
	public void testDawg8() {
		assertTrue(dawg8.getValue(word_cc));
	}

	@Test
	public void testDawg11() {
		assertFalse(DawgFactory.isSingleton(dawg9));
		assertFalse(DawgFactory.isSingleton(dawg10));
		assertTrue(DawgFactory.isSingleton(dawg11));
		assertTrue(dawg11.getValue(word_ab));
	}

	@Test
	public void testDawg12() {
		assertTrue(DawgFactory.isUniversal(dawg12));
	}

	@Test
	public void testDawg13() {
		assertEquals(dawg3, dawg14);
	}

	/**
	 * tests complement operation
	 */
	@Test
	public void test14() {

		final DawgFactory<String, String> dawgFactoryStringString =
				new DawgFactory<String, String>(EprTestHelpers.getEprTheory());
		EprTestHelpers.addConstantsWDefaultSort(dawgFactoryStringString, EprTestHelpers.constantsAbc());

		/*
		 * words in the first automaton
		 */
		final List<String> word_aa = Arrays.asList(new String[] { "a", "a" });

		/*
		 * words not in the first automaton
		 */
		final List<String> word_ab = Arrays.asList(new String[] { "a", "b" });
		final List<String> word_bb = Arrays.asList(new String[] { "b", "b" });

		final SortedSet<String> signature = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signature.addAll(Arrays.asList(new String[] { "u", "w" }));

		final DawgState<String, Boolean> dawgPre = dawgFactoryStringString.createSingletonSet(signature, word_aa);

		assertTrue(dawgPre.getValue(word_aa));
		assertFalse(dawgPre.getValue(word_ab));
		assertFalse(dawgPre.getValue(word_bb));


		final DawgState<String, Boolean> dawgPost = dawgFactoryStringString.createMapped(dawgPre, in -> !in);

		assertFalse(dawgPost.getValue(word_aa));
		assertTrue(dawgPost.getValue(word_ab));
		assertTrue(dawgPost.getValue(word_bb));
	}
}

class EprTheoryMock extends EprTheory {
	public EprTheoryMock(final LogProxy logger) {
		super(logger);
	}
}