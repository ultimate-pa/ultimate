/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Foobar.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

import java.math.BigInteger;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TestCaseWithLogger;

/**
 * A basic test case for the API of SMTInterpol.
 * @author Juergen Christ
 */
public class APITest extends TestCaseWithLogger {
	public APITest() {
		super(Level.ERROR);
	}
	/**
	 * Test what is possible without a logic...
	 */
	public void testNoLogic() {
		SMTInterpol solver = new SMTInterpol(Logger.getRootLogger());
		solver.setOption(":interactive-mode", true);
		try {
			try {
				solver.sort("Bool");
				fail("Could retrieve sort Bool without logic");
			} catch (SMTLIBException expected) {
				System.err.println(expected.getMessage());
			}
			try {
				solver.assertTerm(solver.term("true"));
				fail("Could assert true without logic");
			} catch (SMTLIBException expected) {
				System.err.println(expected.getMessage());
			}
			try {
				solver.checkSat();
				fail("Could check satisfiability without logic");
			} catch (SMTLIBException expected) {
				System.err.println(expected.getMessage());
			}
			try {
				solver.push(1);
				fail("Could push without logic");
			} catch (SMTLIBException expected) {
				System.err.println(expected.getMessage());
			}
			try {
				solver.pop(1);
				fail("Could pop without logic");
			} catch (SMTLIBException expected) {
				System.err.println(expected.getMessage());
			}
			try {
				solver.assertTerm(solver.term("true"));
				fail("Could assert true without logic");
			} catch (SMTLIBException expected) {
				System.err.println(expected.getMessage());
			}
			try {
				solver.getAssertions();
				fail("Could get assertions without logic");
			} catch (SMTLIBException expected) {
				System.err.println(expected.getMessage());
			}
		} catch (Throwable t) {
			fail(t.getMessage());
		}
	}
	
	public void testFaultyLogic() {
		SMTInterpol solver = new SMTInterpol(Logger.getRootLogger());
		try {
			solver.setLogic("TestLogicThatDoesNotExist");
			fail("Could set strange logic!");
		} catch (UnsupportedOperationException expected) {
			System.err.println(expected.getMessage());
		}
	}
	
	public void testPushPop() {
		SMTInterpol solver = new SMTInterpol(Logger.getRootLogger());
		try {
			solver.setLogic(Logics.QF_LIA);
			try {
				solver.push(3);
			} catch (SMTLIBException unexpected) {
				fail(unexpected.getMessage());
			}
			try {
				solver.pop(2);
			} catch (SMTLIBException unexpected) {
				fail(unexpected.getMessage());
			}
			try {
				solver.pop(2);
				fail("Could pop 4 levels after pushing 3");
			} catch (SMTLIBException expected) {
				System.err.println(expected.getMessage());
			}
		} catch (Throwable t) {
			fail(t.getMessage());
		}
	}
	
	public void testSetOptionLate() {
		SMTInterpol solver = new SMTInterpol(Logger.getRootLogger());
		try {
			solver.setLogic(Logics.QF_LIA);
			try {
				solver.setOption(":interactive-mode", true);
				fail("Could activate interactive mode after setting logic");
			} catch (SMTLIBException expected) {
				System.err.println(expected.getMessage());
			}
			try {
				solver.setOption(":produce-proofs", true);
				fail("Could activate proof production after setting logic");
			} catch (SMTLIBException expected) {
				System.err.println(expected.getMessage());
			}
			try {
				solver.setOption(":produce-unsat-cores", true);
				fail("Could activate unsat core production after setting logic");
			} catch (SMTLIBException expected) {
				System.err.println(expected.getMessage());
			}
			try {
				solver.setOption(":produce-assignments", true);
				fail("Could activate assignment production after setting logic");
			} catch (SMTLIBException expected) {
				System.err.println(expected.getMessage());
			}
			try {
				solver.setOption(":interpolant-check-mode", true);
				fail("Could activate interpolant check mode after setting logic");
			} catch (SMTLIBException expected) {
				System.err.println(expected.getMessage());
			}
			try {
				solver.setOption(":unsat-core-check-mode", true);
				fail("Could activate unsat core check mode after setting logic");
			} catch (SMTLIBException expected) {
				System.err.println(expected.getMessage());
			}
		} catch (Throwable t) {
			fail(t.getMessage());
		}
	}
	
	public void testSetLogicTwice() {
		SMTInterpol solver = new SMTInterpol(Logger.getRootLogger());
		try {
			solver.setLogic(Logics.QF_LIA);
			try {
				solver.setLogic(Logics.QF_LIA);
				fail("Could set logic a second time");
			} catch (SMTLIBException expected) {
				System.err.println(expected.getMessage());
			}
			try {
				solver.declareFun("x", new Sort[0], solver.sort("Int"));
				solver.assertTerm(solver.term("=", 
						solver.term("x"), solver.numeral(BigInteger.ZERO)));
				solver.checkSat();
			} catch (SMTLIBException unexpected) {
				fail(unexpected.getMessage());
			}
		} catch (Throwable t) {
			fail(t.getMessage());
		}
	}
	
	public void testTermAssertion() {
		SMTInterpol solver1 = new SMTInterpol(Logger.getRootLogger());
		SMTInterpol solver2 = new SMTInterpol(Logger.getRootLogger());
		try {
			solver1.setLogic(Logics.QF_LIA);
			solver2.setLogic(Logics.QF_LIA);
			solver1.declareFun("x", new Sort[0], solver1.sort("Int"));
			solver2.declareFun("x", new Sort[0], solver2.sort("Int"));
			try {
				solver1.assertTerm(solver2.term("=",
						solver2.term("x"), solver2.numeral(BigInteger.ZERO)));
				fail("Could assert term created by different solver");
			} catch (SMTLIBException expected) {
				System.err.println(expected.getMessage());
			}
			try {
				solver1.assertTerm(solver1.term("x"));
				fail("Could assert non-Boolean term");
			} catch (SMTLIBException expected) {
				System.err.println(expected.getMessage());
			}
			if (Config.STRONG_USAGE_CHECKS) {
				try {
					solver1.assertTerm(solver1.term("=", solver1.term("x"),
							solver1.variable("y", solver1.sort("Int"))));
					fail("Could assert open term");
				} catch (SMTLIBException expected) {
					System.err.println(expected.getMessage());
				}
			} else {
				System.out.println("Skipping closed formula test since strong usage checks are disabled");
			}
		} catch (RuntimeException exc) {
			fail(exc.getMessage());
		}
	}
	
	public void testUndeclared() {
		SMTInterpol solver = new SMTInterpol(Logger.getRootLogger());
		try {
			solver.setLogic(Logics.QF_LIA);
			try {
				solver.term("x");
				fail("Could create undeclared term");
			} catch (SMTLIBException expected) {
				System.err.println(expected.getMessage());
			}
			try {
				solver.variable("x", solver.sort("NOTEXISTENT"));
				fail("Could create variable with unknown sort");
			} catch (SMTLIBException expected) {
				System.err.println(expected.getMessage());
			}
		} catch (Throwable t) {
			fail(t.getMessage());
		}
	}
}
