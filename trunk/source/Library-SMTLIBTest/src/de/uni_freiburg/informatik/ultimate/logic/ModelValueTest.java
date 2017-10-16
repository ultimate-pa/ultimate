/*
 * Copyright (C) 2009-2014 University of Freiburg
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
public class ModelValueTest {

	@Test
	public void test() {
		final Script script = new NoopScript();

		script.setLogic(Logics.QF_AUFLIA);
		final Sort sortInt = script.sort("Int");
		script.declareSort("U", 0);
		final Sort sortU = script.sort("U");
		final Sort sortArray = script.sort("Array", sortInt, sortU);

		final Term term123 = script.term("@123", null, sortInt);
		final Term term0Int = script.term("@0", null, sortInt);
		final Term term0U = script.term("@0", null, sortU);
		final Term term0Array = script.term("@0", null, sortArray);

		// Check that caching of function symbols and application terms works.
		// Also checks that it works for equal but not same strings.
		final String at = "@";
		Assert.assertSame(script.term(at + 123, null, sortInt), term123);
		Assert.assertSame(script.term(at + 0, null, sortInt), term0Int);
		Assert.assertSame(script.term(at + 0, null, sortU), term0U);
		Assert.assertSame(script.term(at + 0, null, sortArray), term0Array);

		// Check that the right symbols were created
		Assert.assertEquals(term123.toString(), "(as @123 Int)");
		Assert.assertEquals(term0Int.toString(), "(as @0 Int)");
		Assert.assertEquals(term0U.toString(), "(as @0 U)");
		Assert.assertEquals(term0Array.toString(), "(as @0 (Array Int U))");
	}
}
