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

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class TermUnifierTest {

	@Test
	public void testBinary() {
		final Theory theory = new Theory(Logics.valueOf("QF_BV"));
		final Term b1 = theory.binary("#b1111");
		final Term b2 = theory.binary("#b1111");

		Assert.assertSame(b1, b2);
	}

	@Test
	public void testHexadecimal() {
		final Theory theory = new Theory(Logics.valueOf("QF_BV"));
		final Term h1 = theory.hexadecimal("#xf");
		final Term h2 = theory.hexadecimal("#xf");

		Assert.assertSame(h1, h2);
	}

	@Test
	public void testDecimal() {
		final Theory theory = new Theory(Logics.valueOf("QF_LRA"));
		final Term d1 = theory.decimal("0.1");
		final Term d2 = theory.decimal("0.1");

		Assert.assertSame(d1, d2);
	}
}
