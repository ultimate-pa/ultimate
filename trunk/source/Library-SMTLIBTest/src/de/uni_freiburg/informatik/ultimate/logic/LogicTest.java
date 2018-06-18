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

import java.math.BigInteger;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class LogicTest {

	@Test
	public void testLIRA() {
		final Theory theory = new Theory(Logics.AUFLIRA);
		final Sort sortInt = theory.getSort("Int");
		final Sort sortReal = theory.getSort("Real");
		Assert.assertNull(theory.getFunction("-"));
		final FunctionSymbol minusInt1 = theory.getFunction("-", sortInt);
		final FunctionSymbol minusInt2 = theory.getFunction("-", sortInt, sortInt);
		Assert.assertNotNull(minusInt1);
		Assert.assertNotNull(minusInt2);
		Assert.assertSame(minusInt2, theory.getFunction("-", sortInt, sortInt, sortInt));
		Assert.assertNull(theory.getFunction("+"));
		Assert.assertNull(theory.getFunction("+", sortInt));
		final FunctionSymbol plusInt2 = theory.getFunction("+", sortInt, sortInt);
		Assert.assertNotNull(plusInt2);
		Assert.assertSame(plusInt2, theory.getFunction("+", sortInt, sortInt, sortInt));

		final FunctionSymbol minusReal1 = theory.getFunction("-", sortReal);
		final FunctionSymbol minusReal2 = theory.getFunction("-", sortReal, sortReal);
		Assert.assertNotNull(minusReal1);
		Assert.assertNotNull(minusReal2);
		Assert.assertSame(minusReal2, theory.getFunction("-", sortReal, sortReal, sortReal));

		Assert.assertNull(theory.getFunction("+", sortReal));
		final FunctionSymbol plusReal2 = theory.getFunction("+", sortReal, sortReal);
		Assert.assertNotNull(plusReal2);
		Assert.assertSame(plusReal2, theory.getFunction("+", sortReal, sortReal, sortReal));
		final FunctionSymbol plusRealIntReal = theory.getFunction("+", sortReal, sortInt, sortReal);
		final FunctionSymbol plusIntIntReal = theory.getFunction("+", sortInt, sortInt, sortReal);
		Assert.assertNotNull(plusRealIntReal);
		Assert.assertNotNull(plusIntIntReal);

		final Term x = theory.term(theory.declareFunction("x", new Sort[0], sortReal));
		final Term y = theory.term(theory.declareFunction("y", new Sort[0], sortReal));
		final Term i = theory.term(theory.declareFunction("i", new Sort[0], sortInt));
		final Term j = theory.term(theory.declareFunction("j", new Sort[0], sortInt));
		final Term sum = theory.term("+", x, y, i, j);
		final Term sum1 = theory.term("+", x, i, y);
		final Term sum2 = theory.term("+", i, j, x);
		Assert.assertSame(plusRealIntReal, ((ApplicationTerm) sum1).getFunction());
		Assert.assertSame(plusIntIntReal, ((ApplicationTerm) sum2).getFunction());
		final Term mul = theory.term("*", Rational.valueOf(-3, 7).toTerm(sortReal), i);
		Assert.assertEquals("(+ x y i j)", sum.toString());
		Assert.assertEquals("(+ x i y)", sum1.toString());
		Assert.assertEquals("(+ i j x)", sum2.toString());
		Assert.assertEquals("(* (/ (- 3.0) 7.0) i)", mul.toString());
	}

	private Sort bitvec(final Theory theory, final int len) {
		return theory.getSort("BitVec", new BigInteger[] { BigInteger.valueOf(len) });
	}

	@Test
	public void testBV() {
		final Theory theory = new Theory(Logics.QF_BV);
		final Term bvABCD = theory.hexadecimal("#xABCD");
		final Term bv1111 = theory.binary("#b1111");
		Assert.assertEquals(bitvec(theory, 16), bvABCD.getSort());// NOCHECKSTYLE
		Assert.assertEquals(bitvec(theory, 4), bv1111.getSort());// NOCHECKSTYLE
		final Term bv2 = theory.term("concat", bvABCD, bv1111);
		Assert.assertEquals(bitvec(theory, 20), bv2.getSort());// NOCHECKSTYLE
		final FunctionSymbol bv5sym =
				theory.getFunctionWithResult("bv5", new BigInteger[] { BigInteger.valueOf(3) }, null);
		final Term bv5 = theory.term(bv5sym);
		final FunctionSymbol bv3sym =
				theory.getFunctionWithResult("bv3", new BigInteger[] { BigInteger.valueOf(5) }, null);
		final Term bv3 = theory.term(bv3sym);
		Assert.assertEquals(bitvec(theory, 3), bv5.getSort());// NOCHECKSTYLE
		Assert.assertEquals(bitvec(theory, 5), bv3.getSort());// NOCHECKSTYLE
		Assert.assertEquals(bitvec(theory, 8), theory.term("concat", bv3, bv5).getSort());// NOCHECKSTYLE
	}
}
