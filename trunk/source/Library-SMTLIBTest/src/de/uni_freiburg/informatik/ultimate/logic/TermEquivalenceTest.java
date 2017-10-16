/*
 * Copyright (C) 2012-2013 University of Freiburg
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

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class TermEquivalenceTest {

	@Test
	public void testEq() {
		final Theory theory = new Theory(Logics.AUFLIRA);
		// (let ((x y)) (forall ((y Int)) (>= y x)))
		// (let ((z y)) (forall ((w Int)) (>= w z)))
		final Sort intSort = theory.getNumericSort();
		final TermVariable x = theory.createTermVariable("x", intSort);
		final TermVariable y = theory.createTermVariable("y", intSort);
		final TermVariable z = theory.createTermVariable("z", intSort);
		final TermVariable w = theory.createTermVariable("w", intSort);
		final Term lhs = theory.let(x, y, theory.forall(new TermVariable[] { y }, theory.term(">=", y, x)));
		final Term rhs = theory.let(z, y, theory.forall(new TermVariable[] { w }, theory.term(">=", w, z)));
		Assert.assertTrue(new TermEquivalence().equal(lhs, rhs));
	}
}
