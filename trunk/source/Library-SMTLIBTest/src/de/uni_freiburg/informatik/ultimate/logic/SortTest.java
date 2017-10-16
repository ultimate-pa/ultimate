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
import java.util.HashMap;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class SortTest {

	@Test
	public void test() {
		final Theory theory = new Theory(Logics.QF_UF);
		theory.declareSort("Int", 0);
		theory.declareSort("Real", 0);
		theory.declareSort("Array", 2);

		final Sort sortInt = theory.getSort("Int");
		final Sort sortReal = theory.getSort("Real");
		final Sort sortArrIntReal = theory.getSort("Array", sortInt, sortReal);

		Assert.assertEquals(sortInt.toString(), "Int");
		Assert.assertEquals(sortReal.toString(), "Real");
		Assert.assertEquals(sortArrIntReal.toString(), "(Array Int Real)");

		theory.defineSort("AIR", 0, sortArrIntReal);
		final Sort sortAIR = theory.getSort("AIR");

		Assert.assertEquals(sortAIR.toString(), "AIR");
		Assert.assertSame(sortAIR.getRealSort(), sortArrIntReal);

		final Sort[] sortParam = theory.createSortVariables("x");
		Assert.assertEquals(sortParam.length, 1);
		Assert.assertEquals(sortParam[0].toString(), "x");

		final Sort sortArrIntX = theory.getSort("Array", sortInt, sortParam[0]);
		Assert.assertEquals(sortArrIntX.toString(), "(Array Int x)");

		theory.defineSort("AIx", 1, sortArrIntX);
		final Sort sortAIR2 = theory.getSort("AIx", sortReal);

		Assert.assertEquals(sortAIR2.toString(), "(AIx Real)");
		Assert.assertSame(sortAIR2.getRealSort(), sortArrIntReal);
	}

	@Test
	public void testRecursive() {
		final Theory theory = new Theory(Logics.QF_UF);
		theory.declareSort("U", 0);
		final Sort sort = theory.getSort("U");
		theory.declareSort("un", 1);
		theory.declareSort("cons", 2);
		final Sort[] typeargs = theory.createSortVariables("X", "Y");
		final Sort consxy = theory.getSort("cons", typeargs);
		final Sort unconsxy = theory.getSort("un", consxy);
		Sort tmp = consxy;
		Sort tmpconcrete = theory.getSort("cons", sort, sort);
		final Sort[] sort2 = new Sort[] { sort, sort };
		for (int i = 0; i < 100; i++) { // NOCHECKSTYLE
			theory.defineSort("rec" + i, 2, tmp);
			tmp = theory.getSort("rec" + i, consxy, unconsxy);
			Assert.assertEquals(tmp.toString(), "(rec" + i + " (cons X Y) (un (cons X Y)))");

			final Sort untmpconcrete = theory.getSort("un", tmpconcrete);
			tmpconcrete = theory.getSort("cons", tmpconcrete, untmpconcrete);

			Assert.assertSame(tmpconcrete, tmp.getRealSort().mapSort(sort2));

			final HashMap<Sort, Sort> unifier = new HashMap<>();
			Assert.assertTrue(tmp.unifySort(unifier, tmpconcrete));
			Assert.assertSame(sort, unifier.get(typeargs[0]));
			Assert.assertSame(sort, unifier.get(typeargs[1]));

			if (i < 10) {
				Assert.assertEquals((46 << i) - 13, tmpconcrete.toString().length());// NOCHECKSTYLE
			}
		}
		Assert.assertEquals("(rec99 (cons X Y) (un (cons X Y)))", tmp.toString());
		Assert.assertEquals("(rec99 (cons U U) (un (cons U U)))", tmp.mapSort(sort2).toString());
		Assert.assertSame(tmpconcrete, tmp.mapSort(sort2).getRealSort());
		/*
		 * Unfortunately, the following test does not work :) Assert.assertEquals(29155963805249276234424173723635,
		 * tmpconcrete.toString().length());
		 */
	}

	@Test
	public void testUnification() {
		final Theory theory = new Theory(Logics.AUFLIRA);

		final Sort sortInt = theory.getSort("Int");
		final Sort sortReal = theory.getSort("Real");
		theory.defineSort("MyInt", 0, sortInt);
		theory.defineSort("MyReal", 0, sortReal);
		final Sort sortMyInt = theory.getSort("MyInt");
		final Sort sortMyReal = theory.getSort("MyReal");
		final Sort sortArrIntReal = theory.getSort("Array", sortMyInt, sortMyReal);

		final Sort[] generic = theory.createSortVariables("Index", "Elem");
		final Sort sortArray = theory.getSort("Array", generic);

		final HashMap<Sort, Sort> unifier = new HashMap<>();
		Assert.assertTrue(generic[0].unifySort(unifier, sortInt));
		Assert.assertTrue(generic[0].unifySort(unifier, sortMyInt.getRealSort()));
		Assert.assertTrue(generic[1].unifySort(unifier, sortMyReal.getRealSort()));
		Assert.assertTrue(generic[1].unifySort(unifier, sortReal.getRealSort()));
		Assert.assertTrue(sortArray.unifySort(unifier, sortArrIntReal.getRealSort()));
	}

	@Test
	public void testIndexedSort() {
		final Theory theory = new Theory(Logics.QF_UF);
		final BigInteger[] size = new BigInteger[] { BigInteger.valueOf(5) };// NOCHECKSTYLE
		final BigInteger[] dim = new BigInteger[] { BigInteger.valueOf(2) };
		final Sort bv5 = new SortSymbol(theory, "bv", 0, null, SortSymbol.INDEXED) {
			@Override
			public void checkArity(final BigInteger[] indices, final int arity) {
				// Disable arity check for this test
			}
		}.getSort(size);// NOCHECKSTYLE
		final Sort marr = new SortSymbol(theory, "MultiArray", 2, null, SortSymbol.INDEXED) {
			@Override
			public void checkArity(final BigInteger[] indices, final int arity) {
				// Disable arity check for this test
			}
		}.getSort(dim, bv5, bv5);// NOCHECKSTYLE
		Assert.assertEquals("(_ bv 5)", bv5.toString());
		Assert.assertEquals("((_ MultiArray 2) (_ bv 5) (_ bv 5))", marr.toString());
	}
}
