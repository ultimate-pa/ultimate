/*
 * Copyright (C) 2012-2013 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import java.math.BigDecimal;
import java.util.Map;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * This test case is designed to test a bug in the selection of possible values for the infinitesimal parameter epsilon.
 * It is designed as a system test and does not directly test the implementation, i.e., the concrete values computed by
 * SMTInterpol. Instead, it checks that the model satisfies the given formula using SMTInterpols model-check-mode
 * 
 * @author Juergen Christ
 */
@RunWith(JUnit4.class)
public class EpsilonTest {

	private SMTInterpol mSolver;
	private Term mInputBase;

	@Before
	public void setUp() throws Exception {
		mSolver = new SMTInterpol(new DefaultLogger());
		mSolver.setOption(":produce-models", Boolean.TRUE);
		mSolver.setLogic(Logics.QF_LRA);
		final Sort real = mSolver.sort("Real");
		mSolver.declareFun("x", Script.EMPTY_SORT_ARRAY, real);
		mSolver.declareFun("y", Script.EMPTY_SORT_ARRAY, real);
		final Term zero = mSolver.decimal(BigDecimal.ZERO);
		final Term one = mSolver.decimal(BigDecimal.ONE);
		final Term threeovertwo = mSolver.decimal(BigDecimal.valueOf(3).divide(// NOCHECKSTYLE
				BigDecimal.valueOf(2)));
		final Term x = mSolver.term("x");
		final Term y = mSolver.term("y");
		mInputBase = mSolver.term("and", mSolver.term("<=", mSolver.term("+", x, y), one), mSolver.term("<", x, zero),
				mSolver.term("<=", y, threeovertwo));
		mSolver.assertTerm(mInputBase);
	}

	@After
	public void tearDown() throws Exception {
		mInputBase = null;
		mSolver.exit();
		mSolver = null;
	}

	@Test
	public void testEmptyProhibitions() {
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
		final Map<Term, Term> eval = mSolver.getValue(new Term[] { mInputBase });
		Assert.assertEquals(1, eval.size());
		Assert.assertSame(mSolver.term("true"), eval.get(mInputBase));
	}

	@Test
	public void testIntervalUpperBound() {
		final Term second = mSolver.term(">", mSolver.term("y"), mSolver.decimal(BigDecimal.ONE));
		mSolver.assertTerm(second);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
		final Map<Term, Term> eval = mSolver.getValue(new Term[] { mInputBase, second });
		Assert.assertEquals(2, eval.size());
		final Term trueTerm = mSolver.term("true");
		Assert.assertSame(trueTerm, eval.get(mInputBase));
		Assert.assertSame(trueTerm, eval.get(second));
	}

	@Test
	public void testProhibHit() {
		final Term second = mSolver.term("not", mSolver.term("=",
				mSolver.term("+", mSolver.term("x"), mSolver.term("y")), mSolver.decimal(BigDecimal.ONE.negate())));
		mSolver.assertTerm(second);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
		final Map<Term, Term> eval = mSolver.getValue(new Term[] { mInputBase, second });
		Assert.assertEquals(2, eval.size());
		final Term trueTerm = mSolver.term("true");
		Assert.assertSame(trueTerm, eval.get(mInputBase));
		Assert.assertSame(trueTerm, eval.get(second));
	}

	@Test
	public void testProhibHitLower() {
		final Term second = mSolver.term("and",
				mSolver.term("not",
						mSolver.term("=", mSolver.term("+", mSolver.term("x"), mSolver.term("y")),
								mSolver.decimal(BigDecimal.ONE.negate()))),
				mSolver.term("not", mSolver.term("=", mSolver.term("x"),
						mSolver.decimal(BigDecimal.ONE.negate().divide(BigDecimal.valueOf(2))))));
		mSolver.assertTerm(second);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
		final Map<Term, Term> eval = mSolver.getValue(new Term[] { mInputBase, second });
		Assert.assertEquals(2, eval.size());
		final Term trueTerm = mSolver.term("true");
		Assert.assertSame(trueTerm, eval.get(mInputBase));
		Assert.assertSame(trueTerm, eval.get(second));
	}

	@Test
	public void testProhibHitNegative() {
		final Term second = mSolver.term("and",
				mSolver.term("not",
						mSolver.term("=", mSolver.term("+", mSolver.term("x"), mSolver.term("y")),
								mSolver.decimal(BigDecimal.ONE.negate()))),
				mSolver.term("not", mSolver.term("=", mSolver.term("x"), mSolver.decimal(BigDecimal.ONE))));
		mSolver.assertTerm(second);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
		final Map<Term, Term> eval = mSolver.getValue(new Term[] { mInputBase, second });
		Assert.assertEquals(2, eval.size());
		final Term trueTerm = mSolver.term("true");
		Assert.assertSame(trueTerm, eval.get(mInputBase));
		Assert.assertSame(trueTerm, eval.get(second));
	}

	@Test
	public void testProhibHitUpper() {
		final Term second = mSolver.term("and",
				mSolver.term("not",
						mSolver.term("=", mSolver.term("+", mSolver.term("x"), mSolver.term("y")),
								mSolver.decimal(BigDecimal.ONE.negate()))),
				mSolver.term("not", mSolver.term("=", mSolver.term("x"), mSolver.decimal(BigDecimal.valueOf(-2)))));// NOCHECKSTYLE
		mSolver.assertTerm(second);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
		final Map<Term, Term> eval = mSolver.getValue(new Term[] { mInputBase, second });
		Assert.assertEquals(2, eval.size());
		final Term trueTerm = mSolver.term("true");
		Assert.assertSame(trueTerm, eval.get(mInputBase));
		Assert.assertSame(trueTerm, eval.get(second));
	}

	@Test
	public void testProhibMiss() {
		final Term second = mSolver.term("not", mSolver.term("=", mSolver.term("x"), mSolver.decimal(BigDecimal.ONE)));
		mSolver.assertTerm(second);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
		final Map<Term, Term> eval = mSolver.getValue(new Term[] { mInputBase, second });
		Assert.assertEquals(2, eval.size());
		final Term trueTerm = mSolver.term("true");
		Assert.assertSame(trueTerm, eval.get(mInputBase));
		Assert.assertSame(trueTerm, eval.get(second));
	}
}
