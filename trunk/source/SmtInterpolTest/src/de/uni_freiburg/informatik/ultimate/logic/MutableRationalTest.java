/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.logic;

import de.uni_freiburg.informatik.ultimate.logic.MutableRational;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import junit.framework.TestCase;

/**
 * Test Class for Rationals.
 * 
 * @author Jochen Hoenicke
 */
public final class MutableRationalTest extends TestCase {
	Rational[] rationals = new RationalTest().rationals;

	public void testAdd() {
		for (int i = 0; i < rationals.length; i++) {
			for (int j = 0; j< rationals.length; j++) {
				MutableRational r1 = new MutableRational(rationals[i]);
				assertSame(r1, r1.add(rationals[j]));
				assertEquals(rationals[i] + " + " + rationals[j],
						rationals[i].add(rationals[j]), r1.toRational());
			}
		}
	}
	
	public void testMul() {
		for (int i = 0; i < rationals.length; i++) {
			for (int j = 0; j< rationals.length; j++) {
				MutableRational r1 = new MutableRational(rationals[i]);
				assertSame(r1, r1.mul(rationals[j]));
				assertEquals(rationals[i] + " * "+rationals[j],
						rationals[i].mul(rationals[j]), r1.toRational());
			}
		}
	}
	
	public void testDiverse() {
		for (int i = 0; i < rationals.length; i++) {
			MutableRational r1 = new MutableRational(rationals[i]);
			assertSame(r1, r1.inverse());
			assertEquals(rationals[i]+".inverse()",
					rationals[i].inverse(), r1.toRational());
			r1 = new MutableRational(rationals[i]);
			assertSame(r1, r1.negate());
			assertEquals(rationals[i]+".negate()",
					rationals[i].negate(), r1.toRational());
			r1 = new MutableRational(rationals[i]);
			assertEquals(rationals[i]+".isIntegral()",
					rationals[i].isIntegral(), r1.isIntegral());
			assertEquals(rationals[i]+".isNegative()",
					rationals[i].isNegative(), r1.isNegative());
			for (int j = 0; j < rationals.length; j++) {
				MutableRational r2 = new MutableRational(rationals[j]);
				assertEquals(rationals[i] + " <=> " + rationals[j],
						rationals[i].compareTo(rationals[j]), r1.compareTo(r2));
			}
		}
	}
}