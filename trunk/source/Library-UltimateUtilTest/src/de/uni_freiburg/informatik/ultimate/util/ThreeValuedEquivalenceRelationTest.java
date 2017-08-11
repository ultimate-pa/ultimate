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

import de.uni_freiburg.informatik.ultimate.util.datastructures.Equality;
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
		
		tver1.reportEquality("x", "y");

		assertFalse(tver1.containsContradiction());
		
		assertTrue(tver1.getEquality("x", "x") == Equality.EQUAL);

		assertTrue(tver1.getEquality("x", "y") == Equality.EQUAL);
		assertTrue(tver1.getEquality("y", "x") == Equality.EQUAL);
		
		tver1.reportNotEquals("x", "z");

		assertFalse(tver1.containsContradiction());

		assertTrue(tver1.getEquality("x", "z") == Equality.NOT_EQUAL);
		assertTrue(tver1.getEquality("z", "x") == Equality.NOT_EQUAL);
		assertTrue(tver1.getEquality("y", "z") == Equality.NOT_EQUAL);
		assertTrue(tver1.getEquality("z", "y") == Equality.NOT_EQUAL);
	
		tver1.reportEquality("a", "b");

		assertTrue(tver1.getEquality("a", "x") == Equality.UNKNOWN);
		
		tver1.reportNotEquals("i", "j");
		
		
		assertTrue(tver1.getEquality("a", "i") == Equality.UNKNOWN);
		assertTrue(tver1.getEquality("x", "i") == Equality.UNKNOWN);
		
		tver1.reportEquality("y", "z");
		
		assertTrue(tver1.containsContradiction());
	
		
	}
}
