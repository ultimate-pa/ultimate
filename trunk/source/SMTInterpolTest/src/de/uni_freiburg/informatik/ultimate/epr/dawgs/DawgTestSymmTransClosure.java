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

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;

/**
 * Test the symmetric transitive closure operation on dawgs (used for equality handling in EPR)
 *
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
@RunWith(JUnit4.class)
public class DawgTestSymmTransClosure {


	/**
	 * Our dawg contains "a a", and "b b", and nothing to connect the two equivalence classes --> the closure should not
	 * put anything the dawg as reflexivity is implied.
	 */
	@Test
	public void test1() {
		final DawgFactory<String, String> dawgFactory = new DawgFactory<String, String>(EprTestHelpers.getEprTheory());
		EprTestHelpers.addConstantsWDefaultSort(dawgFactory, EprTestHelpers.constantsAbc());

		final SortedSet<String> sig = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		sig.add("X");
		sig.add("Y");

		final List<String> word_aa = Arrays.asList(new String[] { "a", "a" });
		final List<String> word_ab = Arrays.asList(new String[] { "a", "b" });
		final List<String> word_ba = Arrays.asList(new String[] { "b", "a" });
		final List<String> word_bb = Arrays.asList(new String[] { "b", "b" });

		DawgState<String, Boolean> dawg = dawgFactory.createSingletonSet(sig, word_aa);
		dawg = dawgFactory.createUnion(dawg, dawgFactory.createSingletonSet(sig, word_bb));

		final DawgState<String, Boolean> dawgRes = dawgFactory.computeSymmetricTransitiveClosure(dawg);

		assertFalse(dawgRes.getValue(word_ab));
		assertFalse(dawgRes.getValue(word_ba));
	}

	/**
	 * The initial dawg contains "a a", "b b", and -connecting the two-, "a b". The resulting dawg should express one
	 * equivalence class "{a b}".
	 */
	@Test
	public void test2() {
		final DawgFactory<String, String> dawgFactory = new DawgFactory<String, String>(EprTestHelpers.getEprTheory());
		EprTestHelpers.addConstantsWDefaultSort(dawgFactory, EprTestHelpers.constantsAbc());

		final SortedSet<String> sig = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		sig.add("X");
		sig.add("Y");

		final List<String> word_aa = Arrays.asList(new String[] { "a", "a" });
		final List<String> word_ab = Arrays.asList(new String[] { "a", "b" });
		final List<String> word_ba = Arrays.asList(new String[] { "b", "a" });
		final List<String> word_bb = Arrays.asList(new String[] { "b", "b" });

		final List<String> word_ac = Arrays.asList(new String[] { "a", "c" });

		final DawgState<String, Boolean> dawg = dawgFactory.createSingletonSet(sig, word_ab);

		final DawgState<String, Boolean> dawgRes = dawgFactory.computeSymmetricTransitiveClosure(dawg);

		assertTrue(dawgRes.getValue(word_ba));
		assertTrue(dawgRes.getValue(word_bb));
		assertFalse(dawgRes.getValue(word_ac));
	}

}
