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
import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;

public class DawgTestProjectColumnAway {

	private EprTheory getEprTheory() {
		return new EprTheoryMock(getLogger());
	}

	private LogProxy getLogger() {
		return new DefaultLogger();
	}

	/**
	 * Example for RenameAndReorder in duplication mode
	 *  - moves from left to right
	 *  - source column is in the middle
	 *  - target column is at the very end
	 *  - just one word in the language
	 *
	 */
	@Test
	public void test1() {
		final DawgFactory<String, String> dawgFactoryStringString =
				new DawgFactory<String, String>(getEprTheory());


		EprTestHelpers.addConstantsWDefaultSort(dawgFactoryStringString, EprTestHelpers.constantsAbc());
//		dawgFactoryStringString.addConstants(getAllConstants());

		final SortedSet<String> signaturePre = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePre.addAll(Arrays.asList(new String[] { "u", "v"}));

		final SortedSet<String> signaturePost = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePost.addAll(Arrays.asList(new String[] { "u" }));


		/*
		 * word in the original automaton
		 */
		final List<String> word_ab = Arrays.asList(new String[] { "a", "b" });

		/*
		 * words that should be in the transformed automaton
		 */
		final List<String> word_abb = Arrays.asList(new String[] { "a", "b", "b" });


//		IDawg<String, String> dawgPre = dawgFactoryStringString.getEmptyDawg(signaturePre);
//		dawgPre = dawgPre.add(word_ab);
//
//		Dawg<String, String> dawgPost = dawgPre.projectColumnAway(column)
////		Dawg<String, String> dawg4 = new ReorderAndRenameDawgBuilder<String, String>(
////					dawgFactoryStringString,
////					(Dawg<String, String>) dawg3,
////					"v",
////					"w",
////					true)
////				.build();
//
//		assertTrue(dawg4.getColNames().equals(signaturePost));
//		assertTrue(dawg4.accepts(word_abb));
	}


}
