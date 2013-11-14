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

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

import junit.framework.TestCase;

public class FunctionTest extends TestCase {
	
	public void test() {
		Theory theory = new Theory(Logics.AUFLIRA);
		
		Sort sortInt   = theory.getSort("Int");
		Sort sortReal  = theory.getSort("Real");
		theory.defineSort("MyInt", 0, sortInt);
		theory.defineSort("MyReal", 0, sortReal);
		Sort sortArrIntReal = theory.getSort("Array", sortInt, sortReal);

		FunctionSymbol select = 
			theory.getFunction("select", sortArrIntReal, sortInt);
		assertNotNull(select);
		assertSame(sortReal, select.getReturnSort());

		FunctionSymbol store = 
			theory.getFunction("store", sortArrIntReal, sortInt, sortReal);
		assertNotNull(store);
		assertSame(sortArrIntReal, store.getReturnSort());

		assertNull(theory.getFunction("select", sortArrIntReal, sortReal));
		assertNull(theory.getFunction("store", sortArrIntReal, sortInt, sortInt));
		
		Sort sortMyInt   = theory.getSort("MyInt");
		Sort sortMyReal  = theory.getSort("MyReal");
		Sort sortArrMyIntMyReal = theory.getSort("Array", sortMyInt, sortMyReal);

		theory.declareSort("List", 1);
		Sort[] typeArgs = theory.createSortVariables("X");
		Sort listx = theory.getSort("List", typeArgs[0]);
		theory.declareInternalPolymorphicFunction("nil", typeArgs, new Sort[0], listx, FunctionSymbol.RETURNOVERLOAD);
		
		assertNull(theory.getFunction("nil"));
		assertNull(theory.getFunctionWithResult("nil", null, sortInt));
		assertNull(theory.getFunctionWithResult("nil", null, sortArrMyIntMyReal));
		
		Sort listInt = theory.getSort("List", sortInt);
		FunctionSymbol nil = theory.getFunctionWithResult("nil", null, listInt);
		assertNotNull(nil);
		assertSame(listInt, nil.getReturnSort());

		Sort listArr = theory.getSort("List", sortArrMyIntMyReal);
		FunctionSymbol nilListArr = theory.getFunctionWithResult("nil", null, listArr);
		assertNotNull(nilListArr);
		assertSame(listArr.getRealSort(), nilListArr.getReturnSort().getRealSort());
		
		theory.defineSort("Heap", 0, listArr);
		Sort heap = theory.getSort("Heap");
		FunctionSymbol nilHeap = theory.getFunctionWithResult("nil", null, heap);
		assertNotNull(nilHeap);
		assertSame(heap, nilHeap.getReturnSort());
		
		theory.declareInternalPolymorphicFunction("car", typeArgs,
				new Sort[] {listx}, typeArgs[0], 0);

		FunctionSymbol carHeap = theory.getFunction("car", heap.getRealSort());
		assertNotNull(carHeap);
		assertSame(sortArrIntReal.getRealSort(), carHeap.getReturnSort());
		Term selcarnilmone = 
			theory.term(select, 
					theory.term(carHeap, theory.term(nilHeap)),
					theory.numeral(BigInteger.ONE.negate()));
		FunctionSymbol eq = 
			theory.getFunction
				("=", new Sort[] { selcarnilmone.getSort(), sortReal });
		Term t = theory.term(eq, selcarnilmone,
					theory.rational(BigInteger.TEN, BigInteger.valueOf(-15)));
		assertSame(theory.getBooleanSort(), t.getSort());
		assertEquals("(= (select (car (as nil Heap)) (- 1)) (/ (- (to_real 2)) (to_real 3)))", t.toString());
	}	
}
