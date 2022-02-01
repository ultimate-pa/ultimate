/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;


/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class ThreeValuedEquivalenceRelationTest {

	@Test
	public void test1() {
		final ThreeValuedEquivalenceRelation<String> tver1 = new ThreeValuedEquivalenceRelation<>();

		tver1.addElement("x");
		tver1.addElement("y");

		tver1.reportEquality("x", "y");

		assertFalse(tver1.isInconsistent());

		assertTrue(tver1.getEqualityStatus("x", "x") == EqualityStatus.EQUAL);

		assertTrue(tver1.getEqualityStatus("x", "y") == EqualityStatus.EQUAL);
		assertTrue(tver1.getEqualityStatus("y", "x") == EqualityStatus.EQUAL);

		tver1.addElement("z");

		tver1.reportDisequality("x", "z");

		assertFalse(tver1.isInconsistent());

		assertTrue(tver1.getEqualityStatus("x", "z") == EqualityStatus.NOT_EQUAL);
		assertTrue(tver1.getEqualityStatus("z", "x") == EqualityStatus.NOT_EQUAL);
		assertTrue(tver1.getEqualityStatus("y", "z") == EqualityStatus.NOT_EQUAL);
		assertTrue(tver1.getEqualityStatus("z", "y") == EqualityStatus.NOT_EQUAL);

		tver1.addElement("a");
		tver1.addElement("b");

		tver1.reportEquality("a", "b");

		assertTrue(tver1.getEqualityStatus("a", "x") == EqualityStatus.UNKNOWN);

		tver1.addElement("i");
		tver1.addElement("j");

		tver1.reportDisequality("i", "j");


		assertTrue(tver1.getEqualityStatus("a", "i") == EqualityStatus.UNKNOWN);
		assertTrue(tver1.getEqualityStatus("x", "i") == EqualityStatus.UNKNOWN);

		tver1.reportEquality("y", "z");

		assertTrue(tver1.isInconsistent());


	}
}
