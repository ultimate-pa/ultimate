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
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;

/**
 * Test Class for Pair Hash.
 *
 * @author Jochen Hoenicke
 */
@RunWith(JUnit4.class)
public final class PairHashTest {
	Theory mTheory;
	CClosure mEngine;
	CCTerm[] mTerms;

	public PairHashTest() {
		mTheory = new Theory(Logics.QF_UF);
		final DPLLEngine dpllEngine = new DPLLEngine(mTheory, new DefaultLogger(), () -> false);
		mEngine = new CClosure(dpllEngine);
		createtermss();
		dpllEngine.getLogger().setLoglevel(LogProxy.LOGLEVEL_DEBUG);
	}

	public void createtermss() {
		mTheory.declareSort("U", 0);
		final Sort sort = mTheory.getSort("U");
		mTerms = new CCTerm[100];// NOCHECKSTYLE
		for (int i = 0; i < 100; i++) {// NOCHECKSTYLE
			final FunctionSymbol sym = mTheory.declareFunction("x" + i, new Sort[0], sort);
			mTerms[i] = mEngine.createFuncTerm(sym, new CCTerm[0], null);
		}
	}

	@Test
	public void testAll() {
		mEngine.createCCEquality(0, mTerms[5], mTerms[7]);// NOCHECKSTYLE
		mEngine.createCCEquality(0, mTerms[3], mTerms[7]);// NOCHECKSTYLE
		mEngine.createCCEquality(0, mTerms[5], mTerms[9]);// NOCHECKSTYLE
		mEngine.createCCEquality(0, mTerms[2], mTerms[11]);// NOCHECKSTYLE
		mEngine.createCCEquality(0, mTerms[15], mTerms[53]);// NOCHECKSTYLE
		mEngine.createCCEquality(0, mTerms[4], mTerms[12]);// NOCHECKSTYLE
		mEngine.createCCEquality(0, mTerms[5], mTerms[13]);// NOCHECKSTYLE
		for (int i = 1; i < 100; i += i) {// NOCHECKSTYLE
			for (int j = 0; j + i < 100; j += 2 * i) {// NOCHECKSTYLE
				mTerms[j].merge(mEngine, mTerms[j + i], mEngine.createCCEquality(1, mTerms[j], mTerms[j + i]));
			}
		}
		mEngine.createCCEquality(0, mTerms[15], mTerms[9]);// NOCHECKSTYLE
		mEngine.createCCEquality(0, mTerms[11], mTerms[32]);// NOCHECKSTYLE
		mEngine.createCCEquality(0, mTerms[3], mTerms[34]);// NOCHECKSTYLE
		mEngine.createCCEquality(0, mTerms[2], mTerms[6]);// NOCHECKSTYLE
		mEngine.createCCEquality(0, mTerms[5], mTerms[12]);// NOCHECKSTYLE
		mEngine.createCCEquality(0, mTerms[4], mTerms[13]);// NOCHECKSTYLE

		for (int i = 64; i >= 1; i /= 2) {// NOCHECKSTYLE
			for (int j = 99 / 2 / i * 2 * i; j >= 0; j -= 2 * i) {// NOCHECKSTYLE
				if (j + i < 100) {// NOCHECKSTYLE
					final CCTerm lhs = mTerms[j];
					final CCTerm rhs = mTerms[j + i];
					final CCTerm tmp = mEngine.mMerges.pop();
					if (tmp == lhs) {
						lhs.mRepStar.invertEqualEdges(mEngine);
						lhs.undoMerge(mEngine, rhs);
					} else {
						assert tmp == rhs;
						rhs.mRepStar.invertEqualEdges(mEngine);
						rhs.undoMerge(mEngine, lhs);
					}
				}
			}
		}
		Assert.assertNotNull(mEngine.mPairHash.getInfo(mTerms[15], mTerms[9]));// NOCHECKSTYLE
		Assert.assertNotNull(mEngine.mPairHash.getInfo(mTerms[11], mTerms[32]));// NOCHECKSTYLE
		Assert.assertNotNull(mEngine.mPairHash.getInfo(mTerms[3], mTerms[34]));// NOCHECKSTYLE
		Assert.assertNotNull(mEngine.mPairHash.getInfo(mTerms[2], mTerms[6]));// NOCHECKSTYLE
	}
}
