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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier.CCTermBuilder;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;

/**
 * Tests the addition of a term congruent to another term and the building of the congruence graph.
 *
 * Tests:
 *
 * 1: x0=x1 and f(x0) then add f(x1) 2: x2=x3 then add f(x2) and f(x3) 3: x4=x5 then add g(f(x4)) and g(f(x5)) 4: add
 * h(x0,x2,x4) and h(x1,x2,x3) 5: a=b and b=c with terms f(b), and f(c) then create f(a), retract b=c, build congruence,
 * and check f(a)=f(b)
 *
 * @author Juergen Christ
 */
@RunWith(JUnit4.class)
public class CongruentAddTest {
	Theory mTheory;
	LogProxy mLogger;
	Clausifier mClausifier;
	SourceAnnotation mSource = new SourceAnnotation("", null);
	DPLLEngine mDPLL;
	CClosure mClosure;
	CCTerm[] mTerms;
	FunctionSymbol mF, mG, mH;
	CCEquality[] mEqualities;
	CCTerm mTermF;
	CCTerm mA, mB, mC, mD;
	CCTerm mFa, mFb, mFc, mFd;
	CCEquality mAB = null, mBC = null, mCD = null;

	public CongruentAddTest() {
		mTheory = new Theory(Logics.QF_UF);
		mLogger = new DefaultLogger();
		mLogger.setLoglevel(LogProxy.LOGLEVEL_DEBUG);
		mDPLL = new DPLLEngine(mTheory, mLogger, () -> false);
		mClausifier = new Clausifier(mDPLL, 0);
		mClausifier.setLogic(Logics.QF_UF);
		mClosure = mClausifier.getCClosure();
		createterms();
	}

	private void createterms() {
		mTheory.declareSort("U", 0);
		final Sort sort = mTheory.getSort("U");
		final Sort[] paramSort = { sort };
		final Sort[] paramSort2 = { sort, sort, sort };
		mF = mTheory.declareFunction("f", paramSort, sort);
		mG = mTheory.declareFunction("g", paramSort, sort);
		mH = mTheory.declareFunction("h", paramSort2, sort);
		mTerms = new CCTerm[6];// NOCHECKSTYLE
		for (int i = 0; i < 6; ++i) {// NOCHECKSTYLE
			final FunctionSymbol sym = mTheory.declareFunction("x" + i, Script.EMPTY_SORT_ARRAY, sort);
			mTerms[i] = mClosure.getFuncTerm(sym);
		}
		final FunctionSymbol funcd = mTheory.declareFunction("d", Script.EMPTY_SORT_ARRAY, sort);
		final FunctionSymbol funcc = mTheory.declareFunction("c", Script.EMPTY_SORT_ARRAY, sort);
		final FunctionSymbol funcb = mTheory.declareFunction("b", Script.EMPTY_SORT_ARRAY, sort);
		final FunctionSymbol funca = mTheory.declareFunction("a", Script.EMPTY_SORT_ARRAY, sort);
		mD = mClosure.getFuncTerm(funcd);
		mC = mClosure.getFuncTerm(funcc);
		mB = mClosure.getFuncTerm(funcb);
		mA = mClosure.getFuncTerm(funca);
		final SharedTerm shareda = mClausifier.getSharedTerm(mTheory.term(funca), mSource);
		final SharedTerm sharedb = mClausifier.getSharedTerm(mTheory.term(funcb), mSource);
		final SharedTerm sharedc = mClausifier.getSharedTerm(mTheory.term(funcc), mSource);
		final SharedTerm sharedd = mClausifier.getSharedTerm(mTheory.term(funcd), mSource);
		final CCTermBuilder builder = mClausifier.new CCTermBuilder(mSource);
		builder.convert(shareda.getTerm());
		builder.convert(sharedb.getTerm());
		builder.convert(sharedc.getTerm());
		builder.convert(sharedd.getTerm());
		final EqualityProxy eqab = mClausifier.createEqualityProxy(shareda, sharedb);
		Assert.assertNotSame(EqualityProxy.getTrueProxy(), eqab);
		Assert.assertNotSame(EqualityProxy.getFalseProxy(), eqab);
		final EqualityProxy eqbc = mClausifier.createEqualityProxy(sharedb, sharedc);
		Assert.assertNotSame(EqualityProxy.getTrueProxy(), eqbc);
		Assert.assertNotSame(EqualityProxy.getFalseProxy(), eqbc);
		final EqualityProxy eqcd = mClausifier.createEqualityProxy(sharedc, sharedd);
		Assert.assertNotSame(EqualityProxy.getTrueProxy(), eqcd);
		Assert.assertNotSame(EqualityProxy.getFalseProxy(), eqcd);
		mAB = (CCEquality) eqab.getLiteral(mSource);
		mBC = (CCEquality) eqbc.getLiteral(mSource);
		mCD = (CCEquality) eqcd.getLiteral(mSource);
		mFc = mClosure.createAppTerm(false, mClosure.getFuncTerm(mF), mC);
		mFb = mClosure.createAppTerm(false, mClosure.getFuncTerm(mF), mB);
		mEqualities = new CCEquality[3];// NOCHECKSTYLE
		for (int i = 0; i < 3; ++i) {
			mEqualities[i] = mClosure.createCCEquality(1, mTerms[2 * i], mTerms[2 * i + 1]);
		}
	}

	@Test
	public void testCase1() {
		final CCTerm t1 = mClosure.createAppTerm(false, mClosure.getFuncTerm(mF), mTerms[0]);
		Clause conflict = mTerms[0].merge(mClosure, mTerms[1], mEqualities[0]);
		Assert.assertNull(conflict);
		final CCTerm t2 = mClosure.createAppTerm(false, mClosure.getFuncTerm(mF), mTerms[1]);
		conflict = mClosure.checkpoint();
		Assert.assertNull(conflict);
		Assert.assertSame(t1.getRepresentative(), t2.getRepresentative());
	}

	@Test
	public void testCase2() {
		Clause conflict = mTerms[2].merge(mClosure, mTerms[3], mEqualities[1]);// NOCHECKSTYLE
		Assert.assertNull(conflict);
		final CCTerm t1 = mClosure.createAppTerm(false, mClosure.getFuncTerm(mF), mTerms[2]);
		final CCTerm t2 = mClosure.createAppTerm(false, mClosure.getFuncTerm(mF), mTerms[3]);
		conflict = mClosure.checkpoint();
		Assert.assertNull(conflict);
		Assert.assertSame(t1.getRepresentative(), t2.getRepresentative());
	}

	@Test
	public void testCase3() {
		Clause conflict = mTerms[4].merge(mClosure, mTerms[5], mEqualities[2]);// NOCHECKSTYLE
		Assert.assertNull(conflict);
		final CCTerm gsub1 = mClosure.createAppTerm(false, mClosure.getFuncTerm(mF), mTerms[4]);
		final CCTerm gsub2 = mClosure.createAppTerm(false, mClosure.getFuncTerm(mF), mTerms[5]);
		Assert.assertNotSame(gsub1.getRepresentative(), gsub2.getRepresentative());
		final CCTerm t1 = mClosure.createAppTerm(false, mClosure.getFuncTerm(mG), gsub1);
		final CCTerm t2 = mClosure.createAppTerm(false, mClosure.getFuncTerm(mG), gsub2);
		Assert.assertNotSame(t1.getRepresentative(), t2.getRepresentative());
		conflict = mClosure.checkpoint();
		Assert.assertNull(conflict);
		Assert.assertSame(t1.getRepresentative(), t2.getRepresentative());
	}

	@Test
	public void testCase4() {
		Clause conflict = mTerms[0].merge(mClosure, mTerms[1], mEqualities[0]);
		Assert.assertNull(conflict);
		conflict = mTerms[2].merge(mClosure, mTerms[3], mEqualities[1]);// NOCHECKSTYLE
		Assert.assertNull(conflict);
		conflict = mTerms[4].merge(mClosure, mTerms[5], mEqualities[2]);// NOCHECKSTYLE
		Assert.assertNull(conflict);
		for (int i = 0; i < 3; ++i) {
			Assert.assertSame(mTerms[2 * i].getRepresentative(), mTerms[2 * i + 1].getRepresentative());
		}
		CCTerm h0 = mClosure.createAppTerm(true, mClosure.getFuncTerm(mH), mTerms[0]);
		CCTerm h02 = mClosure.createAppTerm(true, h0, mTerms[2]);
		CCTerm h024 = mClosure.createAppTerm(false, h02, mTerms[4]);
		CCTerm h1 = mClosure.createAppTerm(true, mClosure.getFuncTerm(mH), mTerms[1]);
		CCTerm h13 = mClosure.createAppTerm(true, h1, mTerms[3]);
		CCTerm h135 = mClosure.createAppTerm(false, h13, mTerms[5]);
		conflict = mClosure.checkpoint();
		Assert.assertNull(conflict);
		Assert.assertSame(h024.getRepresentative(), h135.getRepresentative());
	}

	@Test
	public void testCase5() {
		mDPLL.increaseDecideLevel();
		Clause conflict = mDPLL.setLiteral(mAB);
		Assert.assertNull(conflict);
		mDPLL.increaseDecideLevel();
		conflict = mDPLL.setLiteral(mCD);
		Assert.assertNull(conflict);
		mDPLL.increaseDecideLevel();
		mBC.mStackDepth = mDPLL.getDecideLevel();
		conflict = mDPLL.setLiteral(mBC);
		Assert.assertNull(conflict);
		// System.err.println("a.repStar = " + a.getRepresentative());
		// System.err.println("b.repStar = " + b.getRepresentative());
		// System.err.println("c.repStar = " + c.getRepresentative());
		// Create congruence closure
		conflict = mClosure.checkpoint();
		Assert.assertNull(conflict);
		long time = System.nanoTime();
		mFa = mClosure.createAppTerm(false, mClosure.getFuncTerm(mF), mA);
		time -= System.nanoTime();
		mClosure.mEngine.getLogger().info("f(a)-creation time: " + -time);
		// We can even remove this step and still get an error
		conflict = mClosure.checkpoint();
		Assert.assertNull(conflict);
		// System.err.println("fa.repStar = " + fa.getRepresentative());
		// System.err.println("fb.repStar = " + fb.getRepresentative());
		// System.err.println("fc.repStar = " + fc.getRepresentative());
		Assert.assertSame(mFa.getRepresentative(), mFb.getRepresentative());
		Assert.assertSame(mFb.getRepresentative(), mFc.getRepresentative());
		time = System.nanoTime();
		mFd = mClosure.createAppTerm(false, mClosure.getFuncTerm(mF), mD);
		time -= System.nanoTime();
		mClosure.mEngine.getLogger().info("f(d)-creation time: " + -time);
		conflict = mClosure.checkpoint();
		Assert.assertNull(conflict);
		Assert.assertSame(mFa.getRepresentative(), mFb.getRepresentative());
		Assert.assertSame(mFb.getRepresentative(), mFc.getRepresentative());
		Assert.assertSame(mFc.getRepresentative(), mFd.getRepresentative());
		mDPLL.backtrackLiteral(mBC);
		mClosure.backtrackComplete();
		mDPLL.decreaseDecideLevel();
		conflict = mClosure.checkpoint();
		Assert.assertNull(conflict);
		Assert.assertSame(mA.getRepresentative(), mB.getRepresentative());
		Assert.assertNotSame(mB.getRepresentative(), mC.getRepresentative());
		Assert.assertSame(mC.getRepresentative(), mD.getRepresentative());
		Assert.assertNotSame(mFb.getRepresentative(), mFc.getRepresentative());
		Assert.assertSame(mFc.getRepresentative(), mFd.getRepresentative());
		Assert.assertSame(mFa.getRepresentative(), mFb.getRepresentative());
	}
}
