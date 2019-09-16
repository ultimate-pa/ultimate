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
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.SortedSet;
import java.util.TreeSet;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;

/**
 * Test for the remap() function in the DawgFactory.
 *
 * @author Jochen Hoenicke
 *
 */
public class DawgTestReorder {

	private EprTheory getEprTheory() {
		return new EprTheoryMock(getLogger());
	}

	private LogProxy getLogger() {
		return new DefaultLogger();
	}

	@Test
	public void test1() {
		final DawgFactory<String, String> dawgFactoryStringString =
				new DawgFactory<String, String>(getEprTheory());

		EprTestHelpers.addConstantsWDefaultSort(dawgFactoryStringString, EprTestHelpers.constantsAbc());
//		dawgFactoryStringString.addConstants(getAllConstants());

		final SortedSet<String> signature = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signature.addAll(Arrays.asList(new String[] { "u", "v", "w", "x"}));

		final int[] remap1 = new int[] { 3, 2, 1, 0 };
		final int[] remap2 = new int[] { 1, 0, 2, 3 };
		final int[] remap3 = new int[] { 0, 2, 1, 3 };
		final int[] remap4 = new int[] { 0, 3, 2, 1 };
		final int[] remap5 = new int[] { 2, 0, 1, 3 };
		final int[] remap6 = new int[] { 1, 2, 0, 3 };

		/*
		 * word in the original automaton
		 */
		final String[][] words = new String[][] {
				new String[] { "a", "b",  "c", "c" },
				new String[] { "b", "a",  "d", "d" },
				new String[] { "b", "a",  "c", "c" },
				new String[] { "a", "b",  "d", "d" }
		};

		DawgState<String, Boolean> dawg = dawgFactoryStringString.createConstantDawg(signature, Boolean.FALSE);
		for (final String[] word : words) {
			dawg = dawgFactoryStringString.createUnion(dawg,
					dawgFactoryStringString.createSingletonSet(signature, Arrays.asList(word)));
		}
		for (final String[] word : words) {
			assertTrue(dawg.getValue(Arrays.asList(word)));
		}
		assertTrue(dawg.isTotal());

		final DawgState<String, Boolean> dawg1 = dawgFactoryStringString.remap(dawg, remap1, signature);
		final DawgState<String, Boolean> dawg2 = dawgFactoryStringString.remap(dawg, remap2, signature);
		final DawgState<String, Boolean> dawg3 = dawgFactoryStringString.remap(dawg, remap3, signature);
		final DawgState<String, Boolean> dawg4 = dawgFactoryStringString.remap(dawg, remap4, signature);
		final DawgState<String, Boolean> dawg5 = dawgFactoryStringString.remap(dawg, remap5, signature);
		final DawgState<String, Boolean> dawg6 = dawgFactoryStringString.remap(dawg, remap6, signature);
		assertTrue(dawg1.isTotal());
		assertTrue(dawg2.isTotal());
		assertTrue(dawg3.isTotal());
		assertTrue(dawg4.isTotal());
		assertTrue(dawg5.isTotal());
		assertTrue(dawg6.isTotal());

		assertTrue(dawg1.getValue(Arrays.asList(new String[] { "c", "c", "b", "a" })));
		assertEquals(dawg2, dawg);
		assertTrue(dawg3.getValue(Arrays.asList(new String[] { "a", "c", "b", "c" })));
		assertTrue(dawg4.getValue(Arrays.asList(new String[] { "a", "d", "d", "b" })));
		assertTrue(dawg5.getValue(Arrays.asList(new String[] { "b", "d", "a", "d" })));
		assertTrue(dawg6.getValue(Arrays.asList(new String[] { "c", "b", "a", "c" })));

		// permutation 1-4 are self-inverse
		assertEquals(dawg, dawgFactoryStringString.remap(dawg1, remap1, signature));
		assertEquals(dawg, dawgFactoryStringString.remap(dawg2, remap2, signature));
		assertEquals(dawg, dawgFactoryStringString.remap(dawg3, remap3, signature));
		assertEquals(dawg, dawgFactoryStringString.remap(dawg4, remap4, signature));
		// permutations 5 and 6 are inverses of each other
		assertEquals(dawg, dawgFactoryStringString.remap(dawg5, remap6, signature));
		assertEquals(dawg, dawgFactoryStringString.remap(dawg6, remap5, signature));

	}

}
