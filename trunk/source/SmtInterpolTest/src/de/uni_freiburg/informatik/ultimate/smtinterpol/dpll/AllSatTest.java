package de.uni_freiburg.informatik.ultimate.smtinterpol.dpll;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import junit.framework.TestCase;

public class AllSatTest extends TestCase {

	public void testAllSat() {
		SMTInterpol solver = new SMTInterpol();
		solver.setOption(":verbosity", 2);
		solver.setLogic(Logics.QF_LIA);
		Sort[] empty = new Sort[0];
		Sort intSort = solver.sort("Int");
		solver.declareFun("x", empty, intSort);
		solver.declareFun("y", empty, intSort);
		Term zero = solver.numeral(BigInteger.ZERO);
		solver.assertTerm(solver.term(">=", 
				solver.term("+", solver.term("x"), solver.term("y")),
			zero));
		Term[] important = new Term[] {
				solver.term("<", solver.term("x"), zero),
				solver.term("<", solver.term("y"), zero),
				solver.term("=",
						solver.term("*",
								solver.numeral(BigInteger.valueOf(2)),
								solver.term("x")),
						solver.numeral(BigInteger.ONE)),
				solver.term("=", solver.term("x"), solver.term("x"))
		};
		int cnt = 0;
		for (Term[] minterm : solver.checkAllsat(important)) {
			System.err.println("Found minterm:");
			for (Term t : minterm)
				System.err.println(t);
			++cnt;
		}
		assertEquals(3, cnt);
	}
	
}
