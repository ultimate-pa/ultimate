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

import junit.framework.TestCase;

public class PrintTest extends TestCase {
	
	public void testSort() {
		Theory theory = new Theory(Logics.QF_UFLIA);
		
		Sort sortInt   = theory.getSort("Int");
		Sort sortReal  = theory.getSort("Real");
		theory.defineSort("U'", 0, sortInt);
		theory.defineSort("0AB", 1, sortReal);
		theory.declareSort("~!@$%^&*_+-=<>.?/abyzABYZ0189", 0);
		theory.declareSort("A", 1);
		assertEquals("|U'|", theory.getSort("U'").toString());
		assertEquals("(|0AB| |U'|)", theory.getSort("0AB", theory.getSort("U'")).toString());
		assertEquals("~!@$%^&*_+-=<>.?/abyzABYZ0189", 
				theory.getSort("~!@$%^&*_+-=<>.?/abyzABYZ0189").toString());
		
		StringBuilder expected = new StringBuilder();
		Sort sort = theory.getSort("Int");
		for (int i = 0; i < 10000; i++) {
			sort = theory.getSort("A", sort);
			expected.append("(A ");
		}
		expected.append("Int");
		for (int i = 0; i < 10000; i++) {
			expected.append(")");
		}
		assertEquals(expected.toString(), sort.toString());
	}	

	public void testFun() {
		Theory theory = new Theory(Logics.QF_UFLIA);
		
		Sort sortInt   = theory.getSort("Int");
		Sort[] empty = new Sort[0];
		theory.declareFunction("U'", empty, sortInt);
		theory.declareFunction("0AB", new Sort[] { sortInt }, sortInt);
		theory.declareFunction("~!@$%^&*_+-=<>.?/abyzABYZ0189", empty, sortInt);
		theory.declareFunction("f", new Sort[] { sortInt }, sortInt);
		assertEquals("|U'|", theory.term("U'").toString());
		assertEquals("(|0AB| |U'|)", theory.term("0AB", theory.term("U'")).toString());
		assertEquals("~!@$%^&*_+-=<>.?/abyzABYZ0189", 
				theory.term("~!@$%^&*_+-=<>.?/abyzABYZ0189").toString());
		
		StringBuilder expected = new StringBuilder();
		Term term = theory.term("U'");
		for (int i = 0; i < 10000; i++) {
			term = theory.term("f", term);
			expected.append("(f ");
		}
		expected.append("|U'|");
		for (int i = 0; i < 10000; i++) {
			expected.append(")");
		}
		assertEquals(expected.toString(), term.toStringDirect());
	}	
}
