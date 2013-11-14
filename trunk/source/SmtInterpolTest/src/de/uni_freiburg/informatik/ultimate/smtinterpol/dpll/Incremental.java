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
package de.uni_freiburg.informatik.ultimate.smtinterpol.dpll;


import junit.framework.TestCase;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;


public class Incremental extends TestCase {
	public void testPushPop() throws Exception {
		Logger logger = Logger.getRootLogger();
        // Setup theory and formulae
		Script script = new SMTInterpol(logger);
		script.setLogic(Logics.QF_UFLIA);
		Sort intSort = script.sort("Int");
		script.declareFun("f", new Sort[] {intSort}, intSort);
		script.declareFun("x", new Sort[]{}, intSort);
		// (= (f x) (+ 5 7))
		Term satformula = script.term("=", script.term("f", script.term("x")),
			script.term("+", script.numeral("5"), script.numeral("7")));
		
		// Initial: satformula
		script.assertTerm(satformula);
		script.push(1);
		script.assertTerm(script.term("true"));
		LBool isSat = script.checkSat();
		assertSame(LBool.SAT, isSat);
		script.pop(1);
		// Back at empty initial stack
		script.push(1);
		script.assertTerm(script.term("false"));
		isSat = script.checkSat();
		assertSame(LBool.UNSAT, isSat);
		// Level 1: false
		script.push(1);
		script.assertTerm(script.term("true"));
		// Level 2: true
		script.push(1);
		script.assertTerm(script.term("not", satformula));
		isSat = script.checkSat();
		assertSame(LBool.UNSAT, isSat);// Should be unsat-cached
		script.pop(3);
		isSat = script.checkSat();
		assertSame(LBool.SAT, isSat);
		script.assertTerm(script.term("true"));
		script.assertTerm(script.term("false"));
		isSat = script.checkSat();
		assertSame(LBool.UNSAT, isSat);
//		assertEquals(3, engine.getInterpolants().length);
	}
}
