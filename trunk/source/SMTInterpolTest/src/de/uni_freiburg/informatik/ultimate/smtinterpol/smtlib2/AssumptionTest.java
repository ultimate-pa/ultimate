/*
 * Copyright (C) 2015-2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

import java.math.BigInteger;
import java.util.Map;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;

@RunWith(JUnit4.class)
public class AssumptionTest {

	/**
	 * A test that only executes if Config.STRONG_USAGE_CHECKS is set. It tests that we correctly complain about bad
	 * terms used as assumptions.
	 */
	@Test
	public void badAssumptions() {
		if (Config.STRONG_USAGE_CHECKS) {
			final SMTInterpol solver = new SMTInterpol();
			solver.setLogic(Logics.QF_UFLIA);
			final Sort boolsort = solver.sort("Bool");
			final Sort intsort = solver.sort("Int");
			solver.declareFun("P", Script.EMPTY_SORT_ARRAY, boolsort);
			solver.declareFun("Q", Script.EMPTY_SORT_ARRAY, boolsort);
			solver.declareFun("f", new Sort[] { intsort }, intsort);
			final Term p = solver.term("P");
			final Term q = solver.term("Q");
			final Term notp = solver.term("not", p);
			final Term pandq = solver.term("and", p, q);
			final Term zero = solver.numeral(BigInteger.ZERO);
			final Term fzero = solver.term("f", zero);
			// The actual test
			// 1) assume zero?
			try {
				solver.checkSatAssuming(zero);
				Assert.fail("Solver did not complain about assuming a numeral");
			} catch (final SMTLIBException expected) {
				// This is the expected behaviour!
				// Do we want to check the error message?
			}
			// 2) Assume (and p q)
			try {
				solver.checkSatAssuming(pandq);
				Assert.fail("Solver did not complain about assuming a conjunction");
			} catch (final SMTLIBException expected) {
				// This is the expected behaviour!
				// Do we want to check the error message?
			}
			// 3) Assume non-Boolean term
			try {
				solver.checkSatAssuming(fzero);
				Assert.fail("Solver did not complain about assuming a non-Boolean term");
			} catch (final SMTLIBException expected) {
				// This is the expected behaviour!
				// Do we want to check the error message?
			}
			// Make sure Boolean terms are supported
			// I omit try-catch here since junit takes care of catching the
			// exception and setting the test to failed. I don't want to lose
			// the exception
			// 4) Assume negation
			solver.checkSatAssuming(notp);
			// 5) Multiple assumptions
			solver.checkSatAssuming(p, q, notp);
		}
	}

	/**
	 * A test to check that we don't keep assumptions that should be deleted.
	 */
	@Test
	public void clearRepeatedAssumptions() {
		final SMTInterpol solver = new SMTInterpol();
		solver.setLogic(Logics.QF_UF);
		solver.declareFun("P", Script.EMPTY_SORT_ARRAY, solver.sort("Bool"));
		final Term p = solver.term("P");
		final Term notp = solver.term("not", p);
		LBool isSat = solver.checkSatAssuming(p);
		Assert.assertSame(LBool.SAT, isSat);
		isSat = solver.checkSatAssuming(notp);
		Assert.assertSame(LBool.SAT, isSat);
	}

	/**
	 * Test that conflicting assumptions are handled correctly
	 */
	@Test
	public void conflictingAssumptions() {
		final SMTInterpol solver = new SMTInterpol();
		solver.setLogic(Logics.QF_UF);
		solver.declareFun("P", Script.EMPTY_SORT_ARRAY, solver.sort("Bool"));
		final Term p = solver.term("P");
		final Term notp = solver.term("not", p);
		LBool isSat = solver.checkSatAssuming(p, notp);
		Assert.assertSame(LBool.UNSAT, isSat);
		isSat = solver.checkSatAssuming(notp, p);
		Assert.assertSame(LBool.UNSAT, isSat);
		// But without assumptions we should still be satisfiable
		isSat = solver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
	}

	@Test
	public void modelproduction() {
		final SMTInterpol solver = new SMTInterpol();
		solver.setLogic(Logics.QF_UFLIA);
		final Sort boolsort = solver.sort("Bool");
		final Sort intsort = solver.sort("Int");
		solver.declareFun("P", Script.EMPTY_SORT_ARRAY, boolsort);
		solver.declareFun("Q", Script.EMPTY_SORT_ARRAY, boolsort);
		final Term p = solver.term("P");
		final Term q = solver.term("Q");
		solver.assertTerm(solver.term("or", p, q));
		// Check value of assumption
		LBool isSat = solver.checkSatAssuming(p);
		Assert.assertSame(LBool.SAT, isSat);
		// q is essentially undefined, so I don't check it. Should be false...
		final Term pval = solver.getValue(new Term[] { p }).get(p);
		Assert.assertSame(solver.term("true"), pval);
		// Check value of assumption and derived values
		isSat = solver.checkSatAssuming(solver.term("not", p));
		Assert.assertSame(LBool.SAT, isSat);
		final Map<Term, Term> vals = solver.getValue(new Term[] { p, q });
		Assert.assertSame(solver.term("false"), vals.get(p));
		Assert.assertSame(solver.term("true"), vals.get(q));
		// Check correct unsatisfiability deduction
		isSat = solver.checkSatAssuming(solver.term("not", p), solver.term("not", q));
		Assert.assertSame(LBool.UNSAT, isSat);

	}
	// More tests are needed that test unsat assumption production, proof production, interpolation

	@Test
	public void testAssumptionRemoval() {
		final SMTInterpol solver = new SMTInterpol();
		solver.setLogic(Logics.QF_UFLIA);
		final Sort boolsort = solver.sort("Bool");
		final Sort intsort = solver.sort("Int");
		solver.declareFun("P", Script.EMPTY_SORT_ARRAY, boolsort);
		solver.declareFun("Q", Script.EMPTY_SORT_ARRAY, boolsort);
		final Term p = solver.term("P");
		final Term q = solver.term("Q");
		solver.assertTerm(solver.term("or", p, q));
		LBool isSat = solver.checkSatAssuming(solver.term("not", p));
		// Model should be (not p) q (not r)
		Assert.assertSame(LBool.SAT, isSat);
		// Note that q was essentially a unit clause before. Check that is not
		// stored as unit clause
		solver.assertTerm(solver.term("not", q));
		isSat = solver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
	}
}
