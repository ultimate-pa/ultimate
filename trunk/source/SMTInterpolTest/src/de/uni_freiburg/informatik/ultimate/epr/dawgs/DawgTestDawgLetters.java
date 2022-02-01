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

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetterFactory;

/**
 *
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
@RunWith(JUnit4.class)
public class DawgTestDawgLetters {


	@Test
	public void test1() {
		final DawgFactory<String, String> dawgFactory = new DawgFactory<String, String>(EprTestHelpers.getEprTheory());
		EprTestHelpers.addConstantsWDefaultSort(dawgFactory, EprTestHelpers.constantsAbc());

		final DawgLetterFactory<String> dawgLetterFactory = dawgFactory.getDawgLetterFactory();


		final Set<String> letters1 = new HashSet<String>(Arrays.asList(new String[] { }));

		final DawgLetter<String> sdl1 = dawgLetterFactory.getSimpleDawgLetter(letters1, EprHelpers.getDummySortId());

		// TODO finish test..


//		final DawgFactory<String, String> dawgFactory = new DawgFactory<String, String>(EprTestHelpers.getEprTheory());
//		EprTestHelpers.addConstantsWDefaultSort(dawgFactory, EprTestHelpers.constantsAbc());
//
//		final SortedSet<String> sig = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
//		sig.add("X");
//		sig.add("Y");
//
//		final List<String> word_aa = Arrays.asList(new String[] { "a", "a" });
//		final List<String> word_ab = Arrays.asList(new String[] { "a", "b" });
//		final List<String> word_ba = Arrays.asList(new String[] { "b", "a" });
//		final List<String> word_bb = Arrays.asList(new String[] { "b", "b" });
//
//		IDawg<String, String> dawg = dawgFactory.createOnePointDawg(sig, word_aa);
//		dawg = dawg.add(word_bb);
//
//		Dawg<String, String> dawgRes = dawgFactory.closeDawgUnderSymmetryAndTransitivity((Dawg<String, String>) dawg);
//
//		assertTrue(dawg.intersect(dawgRes.complement()).isEmpty());
//		assertTrue(dawg.complement().intersect(dawgRes).isEmpty());
	}


}
