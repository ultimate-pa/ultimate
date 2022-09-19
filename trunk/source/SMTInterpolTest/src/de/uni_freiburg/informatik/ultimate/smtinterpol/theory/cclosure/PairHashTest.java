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
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol.ProofMode;

/**
 * Test Class for Pair Hash.
 *
 * @author Jochen Hoenicke
 */
@RunWith(JUnit4.class)
public final class PairHashTest {
	private final int NUMTERMS = 100;

	Theory mTheory;
	CClosure mCClosure;
	CCTerm[] mTerms;

	public PairHashTest() {
		mTheory = new Theory(Logics.QF_UF);
		final DPLLEngine dpllEngine = new DPLLEngine(new DefaultLogger(), () -> false);
		final Clausifier clausifier = new Clausifier(mTheory, dpllEngine, ProofMode.NONE);
		mCClosure = new CClosure(clausifier);
		createtermss();
		dpllEngine.getLogger().setLoglevel(LogProxy.LOGLEVEL_DEBUG);
	}

	public void createtermss() {
		mTheory.declareSort("U", 0);
		final Sort sort = mTheory.getSort("U");
		mTerms = new CCTerm[NUMTERMS];
		for (int i = 0; i < NUMTERMS; i++) {
			final FunctionSymbol sym = mTheory.declareFunction("x" + i, new Sort[0], sort);
			final Term term = mTheory.term(sym);
			mTerms[i] = mCClosure.createAnonTerm(term);
			mCClosure.addTerm(mTerms[i], term);
		}
	}

	@Test
	public void testAll() {
		mCClosure.createCCEquality(0, mTerms[5], mTerms[7]);// NOCHECKSTYLE
		mCClosure.createCCEquality(0, mTerms[3], mTerms[7]);// NOCHECKSTYLE
		mCClosure.createCCEquality(0, mTerms[5], mTerms[9]);// NOCHECKSTYLE
		mCClosure.createCCEquality(0, mTerms[2], mTerms[11]);// NOCHECKSTYLE
		mCClosure.createCCEquality(0, mTerms[15], mTerms[53]);// NOCHECKSTYLE
		mCClosure.createCCEquality(0, mTerms[4], mTerms[12]);// NOCHECKSTYLE
		mCClosure.createCCEquality(0, mTerms[5], mTerms[13]);// NOCHECKSTYLE
		mCClosure.increasedDecideLevel(1);
		for (int i = 1; i < 100; i += i) {// NOCHECKSTYLE
			for (int j = 0; j + i < 100; j += 2 * i) {// NOCHECKSTYLE
				mTerms[j].merge(mCClosure, mTerms[j + i], mCClosure.createCCEquality(1, mTerms[j], mTerms[j + i]));
			}
		}
		mCClosure.createCCEquality(0, mTerms[15], mTerms[9]);// NOCHECKSTYLE
		mCClosure.createCCEquality(0, mTerms[11], mTerms[32]);// NOCHECKSTYLE
		mCClosure.createCCEquality(0, mTerms[3], mTerms[34]);// NOCHECKSTYLE
		mCClosure.createCCEquality(0, mTerms[2], mTerms[6]);// NOCHECKSTYLE
		mCClosure.createCCEquality(0, mTerms[5], mTerms[12]);// NOCHECKSTYLE
		mCClosure.createCCEquality(0, mTerms[4], mTerms[13]);// NOCHECKSTYLE

		mCClosure.decreasedDecideLevel(0);
		Assert.assertNotNull(mCClosure.mPairHash.getInfo(mTerms[15], mTerms[9]));// NOCHECKSTYLE
		Assert.assertNotNull(mCClosure.mPairHash.getInfo(mTerms[11], mTerms[32]));// NOCHECKSTYLE
		Assert.assertNotNull(mCClosure.mPairHash.getInfo(mTerms[3], mTerms[34]));// NOCHECKSTYLE
		Assert.assertNotNull(mCClosure.mPairHash.getInfo(mTerms[2], mTerms[6]));// NOCHECKSTYLE
	}
}
