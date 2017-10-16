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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.NoopProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

@RunWith(JUnit4.class)
public class TermCompilerTest {

	private final Script mSolver;
	private final Term mA, mB, mC, mX, mY, mZ, mT, mF, mThree, mFive;
	private final TermCompiler mCompiler;

	public TermCompilerTest() {
		mSolver = new SMTInterpol(new DefaultLogger());
		mSolver.setLogic(Logics.QF_LIA);
		final Sort boolSort = mSolver.sort("Bool");
		final Sort intSort = mSolver.sort("Int");
		final Sort[] empty = {};
		mSolver.declareFun("a", empty, boolSort);
		mSolver.declareFun("b", empty, boolSort);
		mSolver.declareFun("c", empty, boolSort);
		mSolver.declareFun("x", empty, intSort);
		mSolver.declareFun("y", empty, intSort);
		mSolver.declareFun("z", empty, intSort);
		mA = mSolver.term("a");
		mB = mSolver.term("b");
		mC = mSolver.term("c");
		mX = mSolver.term("x");
		mY = mSolver.term("y");
		mZ = mSolver.term("z");
		mT = mSolver.term("true");
		mF = mSolver.term("false");
		mThree = mSolver.numeral("3");
		mFive = mSolver.numeral("5");
		mCompiler = new TermCompiler();
		mCompiler.setProofTracker(new NoopProofTracker());
	}

	@Test
	public void testAnd() {
		Term in = mSolver.term("and", mA, mB);
		Term ex = mSolver.term("not", mSolver.term("or", mSolver.term("not", mA), mSolver.term("not", mB)));
		Term res = mCompiler.transform(in);
		Assert.assertSame(ex, res);
		in = mSolver.term("and", mA, mA);
		res = mCompiler.transform(in);
		Assert.assertSame(mA, res);
		in = mSolver.term("and", mA, mB, mC, mA);
		ex = mSolver.term("not",
				mSolver.term("or", mSolver.term("not", mA), mSolver.term("not", mB), mSolver.term("not", mC)));
		res = mCompiler.transform(in);
		Assert.assertSame(ex, res);
	}

	@Test
	public void testDistinct() {
		Term in = mSolver.term("distinct", mA, mB, mC);
		Term res = mCompiler.transform(in);
		Assert.assertSame(mF, res);
		in = mSolver.term("distinct", mA, mF);
		res = mCompiler.transform(in);
		Assert.assertSame(mA, res);
		in = mSolver.term("distinct", mA, mT);
		res = mCompiler.transform(in);
		Assert.assertSame(mSolver.term("not", mA), res);
		in = mSolver.term("distinct", mF, mA);
		res = mCompiler.transform(in);
		Assert.assertSame(mA, res);
		in = mSolver.term("distinct", mT, mA);
		res = mCompiler.transform(in);
		Assert.assertSame(mSolver.term("not", mA), res);
		in = mSolver.term("distinct", mA, mA);
		res = mCompiler.transform(in);
		Assert.assertSame(mF, res);
		in = mSolver.term("distinct", mA, mSolver.term("not", mA));
		res = mCompiler.transform(in);
		Assert.assertSame(mT, res);
		in = mSolver.term("distinct", mA, mSolver.term("not", mB));
		res = mCompiler.transform(in);
		Assert.assertSame(mSolver.term("=", mA, mB), res);
		in = mSolver.term("distinct", mSolver.term("not", mA), mB);
		res = mCompiler.transform(in);
		Assert.assertSame(mSolver.term("=", mA, mB), res);
		in = mSolver.term("distinct", mA, mB);
		res = mCompiler.transform(in);
		Assert.assertSame(mSolver.term("=", mA, mSolver.term("not", mB)), res);
		in = mSolver.term("distinct", mX, mY, mX);
		res = mCompiler.transform(in);
		Assert.assertSame(mF, res);
		in = mSolver.term("distinct", mX, mY);
		res = mCompiler.transform(in);
		Assert.assertSame(mSolver.term("not", mSolver.term("=", mX, mY)), res);
		in = mSolver.term("distinct", mX, mY, mZ);
		res = mCompiler.transform(in);
		final Term exp = mSolver.term("not",
				mSolver.term("or", mSolver.term("=", mX, mY), mSolver.term("=", mX, mZ), mSolver.term("=", mY, mZ)));
		Assert.assertSame(exp, res);
	}

	@Test
	public void testEq() {
		Term in = mSolver.term("=", mX, mY, mThree, mFive);
		Term res = mCompiler.transform(in);
		Assert.assertSame(res, mF);
		in = mSolver.term("=", mX, mY, mX);
		res = mCompiler.transform(in);
		Assert.assertSame(mSolver.term("=", mX, mY), res);
		in = mSolver.term("=", mX, mX);
		res = mCompiler.transform(in);
		Assert.assertSame(mT, res);
		in = mSolver.term("=", mT, mA, mF);
		res = mCompiler.transform(in);
		Assert.assertSame(mF, res);
		in = mSolver.term("=", mF, mA, mT);
		res = mCompiler.transform(in);
		Assert.assertSame(mF, res);
		in = mSolver.term("=", mA, mB, mT);
		Term exp = mSolver.term("not", mSolver.term("or", mSolver.term("not", mA), mSolver.term("not", mB)));
		res = mCompiler.transform(in);
		Assert.assertSame(exp, res);
		in = mSolver.term("=", mA, mB, mF);
		exp = mSolver.term("not", mSolver.term("or", mA, mB));
		res = mCompiler.transform(in);
		Assert.assertSame(exp, res);
		in = mSolver.term("=", mA, mB, mC, mA);
		exp = mSolver.term("not", mSolver.term("or", mSolver.term("not", mSolver.term("=", mA, mB)),
				mSolver.term("not", mSolver.term("=", mB, mC))));
		res = mCompiler.transform(in);
		Assert.assertSame(exp, res);
	}

	@Test
	public void testIte() {
		Term res = mCompiler.transform(mSolver.term("ite", mT, mA, mB));
		Assert.assertSame(mA, res);
		res = mCompiler.transform(mSolver.term("ite", mF, mA, mB));
		Assert.assertSame(mB, res);
		res = mCompiler.transform(mSolver.term("ite", mC, mA, mA));
		Assert.assertSame(mA, res);
		res = mCompiler.transform(mSolver.term("ite", mC, mT, mF));
		Assert.assertSame(mC, res);
		res = mCompiler.transform(mSolver.term("ite", mC, mF, mT));
		Assert.assertSame(mSolver.term("not", mC), res);
		res = mCompiler.transform(mSolver.term("ite", mC, mT, mA));
		Assert.assertSame(mSolver.term("or", mC, mA), res);
		res = mCompiler.transform(mSolver.term("ite", mC, mF, mA));
		Assert.assertSame(mSolver.term("not", mSolver.term("or", mC, mSolver.term("not", mA))), res);
		res = mCompiler.transform(mSolver.term("ite", mC, mA, mT));
		Assert.assertSame(mSolver.term("or", mSolver.term("not", mC), mA), res);
		res = mCompiler.transform(mSolver.term("ite", mC, mA, mF));
		Assert.assertSame(mSolver.term("not", mSolver.term("or", mSolver.term("not", mC), mSolver.term("not", mA))),
				res);
		final Term cab = mSolver.term("ite", mC, mA, mB);
		res = mCompiler.transform(cab);
		Assert.assertSame(cab, res);
	}

	@Test
	public void testNot() {
		final Term nota = mSolver.term("not", mA);
		Term res = mCompiler.transform(nota);
		Assert.assertSame(nota, res);
		res = mCompiler.transform(mSolver.term("not", nota));
		Assert.assertSame(mA, res);
		res = mCompiler.transform(mSolver.term("not", mT));
		Assert.assertSame(mF, res);
		res = mCompiler.transform(mSolver.term("not", mF));
		Assert.assertSame(mT, res);
	}

	@Test
	public void testOr() {
		Term res = mCompiler.transform(mSolver.term("or", mA, mT));
		Assert.assertSame(mT, res);
		res = mCompiler.transform(mSolver.term("or", mA, mF, mB));
		Assert.assertSame(mSolver.term("or", mA, mB), res);
		res = mCompiler.transform(mSolver.term("or", mA, mA));
		Assert.assertSame(mA, res);
		res = mCompiler.transform(mSolver.term("or", mA, mB, mC, mA));
		Assert.assertSame(mSolver.term("or", mA, mB, mC), res);
	}
}
