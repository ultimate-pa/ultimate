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
public class FunctionTest {

	@Test
	public void test() {
		final Theory theory = new Theory(Logics.AUFLIRA);

		final Sort sortInt = theory.getSort("Int");
		final Sort sortReal = theory.getSort("Real");
		theory.defineSort("MyInt", 0, sortInt);
		theory.defineSort("MyReal", 0, sortReal);
		final Sort sortArrIntReal = theory.getSort("Array", sortInt, sortReal);

		final FunctionSymbol select = theory.getFunction("select", sortArrIntReal, sortInt);
		Assert.assertNotNull(select);
		Assert.assertSame(sortReal, select.getReturnSort());

		final FunctionSymbol store = theory.getFunction("store", sortArrIntReal, sortInt, sortReal);
		Assert.assertNotNull(store);
		Assert.assertSame(sortArrIntReal, store.getReturnSort());

		Assert.assertNull(theory.getFunction("select", sortArrIntReal, sortReal));
		Assert.assertNull(theory.getFunction("store", sortArrIntReal, sortInt, sortInt));

		final Sort sortMyInt = theory.getSort("MyInt");
		final Sort sortMyReal = theory.getSort("MyReal");
		final Sort sortArrMyIntMyReal = theory.getSort("Array", sortMyInt, sortMyReal);

		theory.declareSort("List", 1);
		final Sort[] typeArgs = theory.createSortVariables("X");
		final Sort listx = theory.getSort("List", typeArgs[0]);
		theory.declareInternalPolymorphicFunction("nil", typeArgs, new Sort[0], listx, FunctionSymbol.RETURNOVERLOAD);

		Assert.assertNull(theory.getFunction("nil"));
		Assert.assertNull(theory.getFunctionWithResult("nil", null, sortInt));
		Assert.assertNull(theory.getFunctionWithResult("nil", null, sortArrMyIntMyReal));

		final Sort listInt = theory.getSort("List", sortInt);
		final FunctionSymbol nil = theory.getFunctionWithResult("nil", null, listInt);
		Assert.assertNotNull(nil);
		Assert.assertSame(listInt, nil.getReturnSort());

		final Sort listArr = theory.getSort("List", sortArrMyIntMyReal);
		final FunctionSymbol nilListArr = theory.getFunctionWithResult("nil", null, listArr);
		Assert.assertNotNull(nilListArr);
		Assert.assertSame(listArr.getRealSort(), nilListArr.getReturnSort().getRealSort());

		theory.defineSort("Heap", 0, listArr);
		final Sort heap = theory.getSort("Heap");
		final FunctionSymbol nilHeap = theory.getFunctionWithResult("nil", null, heap);
		Assert.assertNotNull(nilHeap);
		Assert.assertSame(heap, nilHeap.getReturnSort());

		theory.declareInternalPolymorphicFunction("car", typeArgs, new Sort[] { listx }, typeArgs[0], 0);

		final FunctionSymbol carHeap = theory.getFunction("car", heap.getRealSort());
		Assert.assertNotNull(carHeap);
		Assert.assertSame(sortArrIntReal.getRealSort(), carHeap.getReturnSort());
		final Term selcarnilmone = theory.term(select, theory.term(carHeap, theory.term(nilHeap)),
				Rational.MONE.toTerm(sortInt));
		final FunctionSymbol eq = theory.getFunction("=", new Sort[] { selcarnilmone.getSort(), sortReal });
		final Term t = theory.term(eq, selcarnilmone, Rational.valueOf(10, -15).toTerm(sortReal));
		Assert.assertSame(theory.getBooleanSort(), t.getSort());
		Assert.assertEquals("(= (select (car (as nil Heap)) (- 1)) (/ (- 2.0) 3.0))", t.toString());
	}
}
