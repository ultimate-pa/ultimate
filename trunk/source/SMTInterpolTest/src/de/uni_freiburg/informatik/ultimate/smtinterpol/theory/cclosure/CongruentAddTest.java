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
	Clausifier mClausifier;
	SourceAnnotation mSource = new SourceAnnotation("", null);
	CClosure mEngine;
	CCTerm[] mTerms;
	FunctionSymbol mF, mG, mH;
	CCEquality[] mEqualities;
	CCTerm mA, mB, mC, mD;
	CCTerm mFa, mFb, mFc, mFd;
	CCEquality mAB = null, mBC = null, mCD = null;

	public CongruentAddTest() {
		mTheory = new Theory(Logics.QF_UF);
		final DPLLEngine dpllEngine = new DPLLEngine(mTheory, new DefaultLogger(), () -> false);
		mClausifier = new Clausifier(dpllEngine, 0);
		mClausifier.setLogic(Logics.QF_UF);
		mEngine = mClausifier.getCClosure();
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
		final CCTerm[] EMPTY_PARAMS = new CCTerm[0];
		for (int i = 0; i < 6; ++i) {// NOCHECKSTYLE
			final FunctionSymbol sym = mTheory.declareFunction("x" + i, Script.EMPTY_SORT_ARRAY, sort);
			mTerms[i] = mEngine.createFuncTerm(sym, EMPTY_PARAMS, null);
		}
		final FunctionSymbol funcd = mTheory.declareFunction("d", Script.EMPTY_SORT_ARRAY, sort);
		final FunctionSymbol funcc = mTheory.declareFunction("c", Script.EMPTY_SORT_ARRAY, sort);
		final FunctionSymbol funcb = mTheory.declareFunction("b", Script.EMPTY_SORT_ARRAY, sort);
		final FunctionSymbol funca = mTheory.declareFunction("a", Script.EMPTY_SORT_ARRAY, sort);
		mD = mEngine.createFuncTerm(funcd, EMPTY_PARAMS, null);
		mC = mEngine.createFuncTerm(funcc, EMPTY_PARAMS, null);
		mB = mEngine.createFuncTerm(funcb, EMPTY_PARAMS, null);
		mA = mEngine.createFuncTerm(funca, EMPTY_PARAMS, null);
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
		mFc = mEngine.createFuncTerm(mF, new CCTerm[] { mC }, null);
		mFb = mEngine.createFuncTerm(mF, new CCTerm[] { mB }, null);
		mEqualities = new CCEquality[3];// NOCHECKSTYLE
		for (int i = 0; i < 3; ++i) {
			mEqualities[i] = mEngine.createCCEquality(1, mTerms[2 * i], mTerms[2 * i + 1]);
		}
	}

	@Test
	public void testCase1() {
		final CCTerm[] sub1 = { mTerms[0] };
		final CCTerm t1 = mEngine.createFuncTerm(mF, sub1, null);
		Clause conflict = mTerms[0].merge(mEngine, mTerms[1], mEqualities[0]);
		Assert.assertNull(conflict);
		final CCTerm[] sub2 = { mTerms[1] };
		final CCTerm t2 = mEngine.createFuncTerm(mF, sub2, null);
		conflict = mEngine.checkpoint();
		Assert.assertNull(conflict);
		Assert.assertSame(t1.getRepresentative(), t2.getRepresentative());
	}

	@Test
	public void testCase2() {
		Clause conflict = mTerms[2].merge(mEngine, mTerms[3], mEqualities[1]);// NOCHECKSTYLE
		Assert.assertNull(conflict);
		final CCTerm[] sub1 = { mTerms[2] };
		final CCTerm[] sub2 = { mTerms[3] };// NOCHECKSTYLE
		final CCTerm t1 = mEngine.createFuncTerm(mF, sub1, null);
		final CCTerm t2 = mEngine.createFuncTerm(mF, sub2, null);
		conflict = mEngine.checkpoint();
		Assert.assertNull(conflict);
		Assert.assertSame(t1.getRepresentative(), t2.getRepresentative());
	}

	@Test
	public void testCase3() {
		Clause conflict = mTerms[4].merge(mEngine, mTerms[5], mEqualities[2]);// NOCHECKSTYLE
		Assert.assertNull(conflict);
		final CCTerm[] sub1 = { mTerms[4] };// NOCHECKSTYLE
		final CCTerm[] sub2 = { mTerms[5] };// NOCHECKSTYLE
		final CCTerm[] gsub1 = { mEngine.createFuncTerm(mF, sub1, null) };
		final CCTerm[] gsub2 = { mEngine.createFuncTerm(mF, sub2, null) };
		Assert.assertNotSame(gsub1[0].getRepresentative(), gsub2[0].getRepresentative());
		final CCTerm t1 = mEngine.createFuncTerm(mG, gsub1, null);
		final CCTerm t2 = mEngine.createFuncTerm(mG, gsub2, null);
		Assert.assertNotSame(t1.getRepresentative(), t2.getRepresentative());
		conflict = mEngine.checkpoint();
		Assert.assertNull(conflict);
		Assert.assertSame(t1.getRepresentative(), t2.getRepresentative());
	}

	@Test
	public void testCase4() {
		Clause conflict = mTerms[0].merge(mEngine, mTerms[1], mEqualities[0]);
		Assert.assertNull(conflict);
		conflict = mTerms[2].merge(mEngine, mTerms[3], mEqualities[1]);// NOCHECKSTYLE
		Assert.assertNull(conflict);
		conflict = mTerms[4].merge(mEngine, mTerms[5], mEqualities[2]);// NOCHECKSTYLE
		Assert.assertNull(conflict);
		final CCTerm[] args1 = { mTerms[0], mTerms[2], mTerms[4] };// NOCHECKSTYLE
		final CCTerm[] args2 = { mTerms[1], mTerms[3], mTerms[5] };// NOCHECKSTYLE
		for (int i = 0; i < 3; ++i) {
			Assert.assertSame(mTerms[2 * i].getRepresentative(), mTerms[2 * i + 1].getRepresentative());
		}
		final CCTerm t1 = mEngine.createFuncTerm(mH, args1, null);
		final CCTerm t2 = mEngine.createFuncTerm(mH, args2, null);
		conflict = mEngine.checkpoint();
		Assert.assertNull(conflict);
		Assert.assertSame(t1.getRepresentative(), t2.getRepresentative());
	}

	@Test
	public void testCase5() {
		Clause conflict = mEngine.setLiteral(mAB);
		Assert.assertNull(conflict);
		conflict = mEngine.setLiteral(mCD);
		Assert.assertNull(conflict);
		conflict = mEngine.setLiteral(mBC);
		Assert.assertNull(conflict);
		// System.err.println("a.repStar = " + a.getRepresentative());
		// System.err.println("b.repStar = " + b.getRepresentative());
		// System.err.println("c.repStar = " + c.getRepresentative());
		// Create congruence closure
		conflict = mEngine.checkpoint();
		Assert.assertNull(conflict);
		long time = System.nanoTime();
		mFa = mEngine.createFuncTerm(mF, new CCTerm[] { mA }, null);
		time -= System.nanoTime();
		mEngine.mEngine.getLogger().info("f(a)-creation time: " + -time);
		// We can even remove this step and still get an error
		conflict = mEngine.checkpoint();
		Assert.assertNull(conflict);
		// System.err.println("fa.repStar = " + fa.getRepresentative());
		// System.err.println("fb.repStar = " + fb.getRepresentative());
		// System.err.println("fc.repStar = " + fc.getRepresentative());
		Assert.assertSame(mFa.getRepresentative(), mFb.getRepresentative());
		Assert.assertSame(mFb.getRepresentative(), mFc.getRepresentative());
		time = System.nanoTime();
		mFd = mEngine.createFuncTerm(mF, new CCTerm[] { mD }, null);
		time -= System.nanoTime();
		mEngine.mEngine.getLogger().info("f(d)-creation time: " + -time);
		conflict = mEngine.checkpoint();
		Assert.assertNull(conflict);
		Assert.assertSame(mFa.getRepresentative(), mFb.getRepresentative());
		Assert.assertSame(mFb.getRepresentative(), mFc.getRepresentative());
		Assert.assertSame(mFc.getRepresentative(), mFd.getRepresentative());
		mEngine.backtrackLiteral(mBC);
		conflict = mEngine.checkpoint();
		Assert.assertNull(conflict);
		Assert.assertSame(mA.getRepresentative(), mB.getRepresentative());
		Assert.assertNotSame(mB.getRepresentative(), mC.getRepresentative());
		Assert.assertSame(mC.getRepresentative(), mD.getRepresentative());
		Assert.assertNotSame(mFb.getRepresentative(), mFc.getRepresentative());
		Assert.assertSame(mFc.getRepresentative(), mFd.getRepresentative());
		Assert.assertSame(mFa.getRepresentative(), mFb.getRepresentative());
	}
}
