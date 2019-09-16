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

import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;

@RunWith(JUnit4.class)
public class DawgTestSignatureTranslations {

	private EprTheory getEprTheory() {
		return new EprTheoryMock(getLogger());
	}

	private LogProxy getLogger() {
		return new DefaultLogger();
	}

	@Test
	public void test1() {

		final DawgFactory<String, Integer> dawgFactoryStringInteger =
				new DawgFactory<String, Integer>(getEprTheory());
		EprTestHelpers.addConstantsWDefaultSort(dawgFactoryStringInteger, EprTestHelpers.constantsAbc());



		final List<String> word_aa = Arrays.asList(new String[] { "a", "a" });
		final List<String> word_ab = Arrays.asList(new String[] { "a", "b" });
		final List<String> word_ac = Arrays.asList(new String[] { "a", "c" });
		final List<String> word_ba = Arrays.asList(new String[] { "b", "a" });
		final List<String> word_bb = Arrays.asList(new String[] { "b", "b" });
		final List<String> word_bc = Arrays.asList(new String[] { "b", "c" });
		final List<String> word_ca = Arrays.asList(new String[] { "c", "a" });
		final List<String> word_cb = Arrays.asList(new String[] { "c", "b" });
		final List<String> word_cc = Arrays.asList(new String[] { "c", "c" });


		final SortedSet<Integer> signature1 = new TreeSet<Integer>(EprHelpers.getColumnNamesComparator());
		signature1.addAll(Arrays.asList(new Integer[] { 1, 2 }));

		DawgState<String, Boolean> dawg1 = dawgFactoryStringInteger.createConstantDawg(signature1, Boolean.FALSE);
		dawg1 = dawgFactoryStringInteger.createUnion(dawg1,
				dawgFactoryStringInteger.createSingletonSet(signature1, word_ba));
		dawg1 = dawgFactoryStringInteger.createUnion(dawg1,
				dawgFactoryStringInteger.createSingletonSet(signature1, word_ca));

		assertTrue(dawg1.getValue(word_ba));
		assertTrue(dawg1.getValue(word_ca));

		final SortedSet<Integer> signature2 = new TreeSet<Integer>(EprHelpers.getColumnNamesComparator());
		signature2.addAll(Arrays.asList(new Integer[] { 10, 20, 30 }));

		final int[] translation1 = new int[] { 2, 0 };
		final String[] argList1 = new String[] { null, "d", null };


		final DawgState<String, Boolean> dawg2 = dawgFactoryStringInteger.translateClauseSigToPredSig(dawg1,
				translation1, argList1, signature2);

		assertTrue(dawg2.getValue(Arrays.asList(new String[] { "a", "d", "b" })));
		assertTrue(dawg2.getValue(Arrays.asList(new String[] { "a", "d", "c" })));

	}

	@Test
	public void test2() {

		final DawgFactory<String, Integer> dawgFactoryStringInteger =
				new DawgFactory<String, Integer>(getEprTheory());
		EprTestHelpers.addConstantsWDefaultSort(dawgFactoryStringInteger, EprTestHelpers.constantsAbc());



		final List<String> word_a = Arrays.asList(new String[] { "a" });
		final List<String> word_b = Arrays.asList(new String[] { "b" });
		final List<String> word_c = Arrays.asList(new String[] { "c" });
//		List<String> word_ab = Arrays.asList(new String[] { "a", "b" });
//		List<String> word_ac = Arrays.asList(new String[] { "a", "c" });
//		List<String> word_ba = Arrays.asList(new String[] { "b", "a" });
//		List<String> word_bb = Arrays.asList(new String[] { "b", "b" });
//		List<String> word_bc = Arrays.asList(new String[] { "b", "c" });
//		List<String> word_ca = Arrays.asList(new String[] { "c", "a" });
//		List<String> word_cb = Arrays.asList(new String[] { "c", "b" });
//		List<String> word_cc = Arrays.asList(new String[] { "c", "c" });


		final SortedSet<Integer> signature1 = new TreeSet<Integer>(EprHelpers.getColumnNamesComparator());
		signature1.addAll(Arrays.asList(new Integer[] { 1 }));

		DawgState<String, Boolean> dawg1 = dawgFactoryStringInteger.createConstantDawg(signature1, Boolean.FALSE);
		dawg1 = dawgFactoryStringInteger.createUnion(dawg1,
				dawgFactoryStringInteger.createSingletonSet(signature1, word_a));
		dawg1 = dawgFactoryStringInteger.createUnion(dawg1,
				dawgFactoryStringInteger.createSingletonSet(signature1, word_b));

		assertTrue(dawg1.getValue(word_a));
		assertTrue(dawg1.getValue(word_b));

		final SortedSet<Integer> signature2 = new TreeSet<Integer>(EprHelpers.getColumnNamesComparator());
		signature2.addAll(Arrays.asList(new Integer[] { 10, 20 }));

		final int[] translation1 = new int[] { 0 };
		final String[] argList1 = new String[] { null, "c" };


		final DawgState<String, Boolean> dawg2 =
				dawgFactoryStringInteger.translateClauseSigToPredSig(dawg1, translation1, argList1, signature2);

		assertTrue(dawg2.getValue(Arrays.asList(new String[] { "a", "c" })));
		assertTrue(dawg2.getValue(Arrays.asList(new String[] { "b", "c" })));

	}

}
