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

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

import junit.framework.TestCase;

public class SortTest extends TestCase {
	
	public void test() {
		Theory theory = new Theory(Logics.QF_UF);
		theory.declareSort("Int", 0);
		theory.declareSort("Real", 0);
		theory.declareSort("Array", 2);
		
		Sort sortInt = theory.getSort("Int");
		Sort sortReal = theory.getSort("Real");
		Sort sortArrIntReal = theory.getSort("Array", sortInt, sortReal);

		assertEquals(sortInt.toString(), "Int");
		assertEquals(sortReal.toString(), "Real");
		assertEquals(sortArrIntReal.toString(), "(Array Int Real)");

		theory.defineSort("AIR", 0, sortArrIntReal);
		Sort sortAIR = theory.getSort("AIR");

		assertEquals(sortAIR.toString(), "AIR");
		assertSame(sortAIR.getRealSort(), sortArrIntReal);
		
		Sort[] sortParam = theory.createSortVariables("x");
		assertEquals(sortParam.length, 1);
		assertEquals(sortParam[0].toString(), "x");

		Sort sortArrIntX = theory.getSort("Array", sortInt, sortParam[0]);
		assertEquals(sortArrIntX.toString(), "(Array Int x)");

		
		theory.defineSort("AIx", 1, sortArrIntX);
		Sort sortAIR2 = theory.getSort("AIx", sortReal);
		
		assertEquals(sortAIR2.toString(), "(AIx Real)");
		assertSame(sortAIR2.getRealSort(), sortArrIntReal);
	}
	
	public void testRecursive() {
		Theory theory = new Theory(Logics.QF_UF);
		theory.declareSort("U", 0);
		Sort sort = theory.getSort("U");
		theory.declareSort("un", 1);
		theory.declareSort("cons", 2);
		Sort[] typeargs = theory.createSortVariables("X", "Y");
		Sort consxy = theory.getSort("cons", typeargs);
		Sort unconsxy = theory.getSort("un", consxy);
		Sort tmp = consxy;
		Sort tmpconcrete = theory.getSort("cons", sort, sort);
		Sort[] sort2 = new Sort[] { sort, sort };
		for (int i = 0; i < 100; i++) {
			theory.defineSort("rec"+i, 2, tmp);
			tmp = theory.getSort("rec"+i, consxy, unconsxy);
			assertEquals(tmp.toString(), "(rec"+i+" (cons X Y) (un (cons X Y)))");
			
			Sort untmpconcrete = theory.getSort("un", tmpconcrete);
			tmpconcrete = theory.getSort("cons", tmpconcrete, untmpconcrete);

			assertSame(tmpconcrete, tmp.getRealSort().mapSort(sort2));
				
			HashMap<Sort,Sort> unifier = new HashMap<Sort, Sort>();
			assertTrue(tmp.unifySort(unifier, tmpconcrete));
			assertSame(sort, unifier.get(typeargs[0]));
			assertSame(sort, unifier.get(typeargs[1]));
			
			if (i < 10)
				assertEquals((46 << i)-13, tmpconcrete.toString().length());
		}
		assertEquals("(rec99 (cons X Y) (un (cons X Y)))", tmp.toString());
		assertEquals("(rec99 (cons U U) (un (cons U U)))", tmp.mapSort(sort2).toString());
		assertSame(tmpconcrete, tmp.mapSort(sort2).getRealSort());
		/* Unfortunately, the following test does not work :) 
		 * assertEquals(29155963805249276234424173723635, tmpconcrete.toString().length()); 
		 */
	}
	
	public void testUnification() {
		Theory theory = new Theory(Logics.AUFLIRA);
		
		Sort sortInt   = theory.getSort("Int");
		Sort sortReal  = theory.getSort("Real");
		theory.defineSort("MyInt", 0, sortInt);
		theory.defineSort("MyReal", 0, sortReal);
		Sort sortMyInt = theory.getSort("MyInt");
		Sort sortMyReal = theory.getSort("MyReal");
		Sort sortArrIntReal = theory.getSort("Array", sortMyInt, sortMyReal);
		
		Sort[] generic = theory.createSortVariables("Index", "Elem");
		Sort sortArray = theory.getSort("Array", generic);
		
		HashMap<Sort,Sort> unifier = new HashMap<Sort, Sort>();
		assertTrue(generic[0].unifySort(unifier, sortInt));
		assertTrue(generic[0].unifySort(unifier, sortMyInt.getRealSort()));
		assertTrue(generic[1].unifySort(unifier, sortMyReal.getRealSort()));
		assertTrue(generic[1].unifySort(unifier, sortReal.getRealSort()));
		assertTrue(sortArray.unifySort(unifier, sortArrIntReal.getRealSort()));
	}
	
	public void testIndexedSort() {
		Theory theory = new Theory(Logics.QF_UF);
		BigInteger[] size = new BigInteger[] { BigInteger.valueOf(5) };
		BigInteger[] dim  = new BigInteger[] { BigInteger.valueOf(2) };
		Sort bv5 = new SortSymbol(theory, "bv", 0, null, SortSymbol.INDEXED) {
			public void checkArity(BigInteger[] indices, int arity) {}
		}.getSort(size);
		Sort marr = new SortSymbol(theory, "MultiArray", 2, null, SortSymbol.INDEXED) {
			public void checkArity(BigInteger[] indices, int arity) {}
		}.getSort(dim, bv5, bv5);
		assertEquals("(_ bv 5)", bv5.toString());
		assertEquals("((_ MultiArray 2) (_ bv 5) (_ bv 5))", marr.toString());
	}
}
