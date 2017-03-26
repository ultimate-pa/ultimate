/*
 * Copyright (C) 2016 Jens Stimpfle <stimpflj@informatik.uni-freiburg.de>

 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 3 of the License,
 * or (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be
 * useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser
 * General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see
 * <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automata Library, or any covered work, by linking or combining it
 * with Eclipse RCP (or a modified version of Eclipse RCP), containing parts
 * covered by the terms of the Eclipse Public License, the licensors of the
 * ULTIMATE Automata Library grant you additional permission to convey the
 * resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.arrays;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;

/**
 * Formulate "merge relation constraints" (as defined in my thesis) as a MAX-SAT instance.
 * <p>
 * A solution to the instance can be converted to a merge relation later.
 *
 * @author stimpflj
 */
final class Generator {

	private Generator() {
		// no public constructor
	}

	/**
	 * Convert a solved instance to a merge relation
	 */
	static Partition makeMergeRelation(final int numStates, final char[] assigned) {
		final UnionFind unionFind = new UnionFind(numStates);
		final EqVarCalc calc = new EqVarCalc(numStates);

		assert assigned.length == calc.getNumEqVars();

		for (final int x : assigned) {
			assert x == Solver.TRUE || x == Solver.FALSE;
		}

		for (int i = 0; i < numStates; i++) {
			for (int j = i + 1; j < numStates; j++) {
				final int eqVar = calc.eqVar(i, j);
				if (assigned[eqVar] == Solver.TRUE) {
					unionFind.merge(i, j);
				}
			}
		}

		return Partition.compress(unionFind.extractRoots());
	}

	/**
	 * @param services
	 *            Ultimate services
	 * @param inNwa
	 *            input NWA.
	 * @param history
	 *            precalculated history states for <code>inNWA</code>.
	 * @return A (consistent) Partition which represents the minimized automaton.
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	static Horn3Array generateClauses(final AutomataLibraryServices services, final NwaWithArrays inNwa,
			ArrayList<Hist> history) throws AutomataOperationCanceledException {
		assert Hist.checkConsistency(inNwa, history);

		// "assert" that there are no transitions which are never taken
		{
			final HashSet<Hist> hs = new HashSet<Hist>();
			for (final Hist h : history) {
				hs.add(h);
			}
			for (final RTrans x : inNwa.mRTrans) {
				assert hs.contains(new Hist(x.mSrc, x.mTop));
			}
		}

		// some "namespace imports"
		final int numStates = inNwa.mNumStates;
		//@SuppressWarnings("unused") int numISyms = inNWA.numISyms;
		//@SuppressWarnings("unused") int numCSyms = inNWA.numCSyms;
		//@SuppressWarnings("unused") int numRSyms = inNWA.numRSyms;
		//@SuppressWarnings("unused") boolean[] isInitial = inNWA.isInitial;
		final boolean[] isFinal = inNwa.mIsFinal;
		final int numITrans = inNwa.mITrans.length;
		final int numCTrans = inNwa.mCTrans.length;
		final int numRTrans = inNwa.mRTrans.length;
		final ITrans[] iTrans = inNwa.mITrans.clone();
		final CTrans[] cTrans = inNwa.mCTrans.clone();
		final RTrans[] rTrans = inNwa.mRTrans.clone();
		final RTrans[] rTransTop = inNwa.mRTrans.clone();

		history = new ArrayList<Hist>(history);

		// IMPORTANT. Sort inputs
		Arrays.sort(iTrans, ITrans::compareSrcSymDst);
		Arrays.sort(cTrans, CTrans::compareSrcSymDst);
		Arrays.sort(rTrans, RTrans::compareSrcSymTopDst);
		Arrays.sort(rTransTop, RTrans::compareSrcTopSymDst);

		history.sort(Hist::compareLinHier);

		// All "outgoing" transitions, grouped by src, then sorted by (top), sym, dst
		final ArrayList<ArrayList<ITrans>> iTransOut = new ArrayList<ArrayList<ITrans>>();
		final ArrayList<ArrayList<CTrans>> cTransOut = new ArrayList<ArrayList<CTrans>>();
		final ArrayList<ArrayList<RTrans>> rTransOut = new ArrayList<ArrayList<RTrans>>();

		for (int i = 0; i < numStates; i++) {
			iTransOut.add(new ArrayList<ITrans>());
		}
		for (int i = 0; i < numStates; i++) {
			cTransOut.add(new ArrayList<CTrans>());
		}
		for (int i = 0; i < numStates; i++) {
			rTransOut.add(new ArrayList<RTrans>());
		}

		for (int i = 0; i < numITrans; i++) {
			iTransOut.get(iTrans[i].mSrc).add(iTrans[i]);
		}
		for (int i = 0; i < numCTrans; i++) {
			cTransOut.get(cTrans[i].mSrc).add(cTrans[i]);
		}
		for (int i = 0; i < numRTrans; i++) {
			rTransOut.get(rTrans[i].mSrc).add(rTrans[i]);
		}

		final IntArray[] iSet = new IntArray[numStates];
		final IntArray[] cSet = new IntArray[numStates];
		final IntArray[] rSet = new IntArray[numStates];
		final IntArray[] rTop = new IntArray[numStates];
		final IntArray[] hSet = new IntArray[numStates];

		for (int i = 0; i < numStates; i++) {
			iSet[i] = new IntArray();
		}
		for (int i = 0; i < numStates; i++) {
			cSet[i] = new IntArray();
		}
		for (int i = 0; i < numStates; i++) {
			rSet[i] = new IntArray();
		}
		for (int i = 0; i < numStates; i++) {
			rTop[i] = new IntArray();
		}
		for (int i = 0; i < numStates; i++) {
			hSet[i] = new IntArray();
		}

		for (int i = 0; i < numITrans; i++) {
			if (i == 0 || iTrans[i - 1].mSrc != iTrans[i].mSrc || iTrans[i - 1].mSym != iTrans[i].mSym) {
				iSet[iTrans[i].mSrc].add(iTrans[i].mSym);
			}
		}
		for (int i = 0; i < numCTrans; i++) {
			if (i == 0 || cTrans[i - 1].mSrc != cTrans[i].mSrc || cTrans[i - 1].mSym != cTrans[i].mSym) {
				cSet[cTrans[i].mSrc].add(cTrans[i].mSym);
			}
		}
		for (int i = 0; i < numRTrans; i++) {
			if (i == 0 || rTrans[i - 1].mSrc != rTrans[i].mSrc || rTrans[i - 1].mSym != rTrans[i].mSym) {
				rSet[rTrans[i].mSrc].add(rTrans[i].mSym);
			}
		}
		for (int i = 0; i < numRTrans; i++) {
			if (i == 0 || rTransTop[i - 1].mSrc != rTransTop[i].mSrc || rTransTop[i - 1].mTop != rTransTop[i].mTop) {
				rTop[rTransTop[i].mSrc].add(rTransTop[i].mTop);
			}
		}

		{
			// make the hSet, i.e. those history states except bottom-of-stack
			// symbol which are not in the outgoing return transitions as
			// top-of-stack symbol.
			int i = 0;
			for (final Hist h : history) {
				for (; i < numRTrans; i++) {
					if (h.mLin < rTransTop[i].mSrc || (h.mLin == rTransTop[i].mSrc && h.mHier <= rTransTop[i].mTop)) {
						break;
					}
				}
				if (i == numRTrans || h.mLin < rTransTop[i].mSrc
						|| (h.mLin == rTransTop[i].mSrc && h.mHier < rTransTop[i].mTop)) {
					if (h.mHier >= 0) {
						hSet[h.mLin].add(h.mHier);
					}
				}
			}
		}

		for (int i = 0; i < numStates; i++) {
			for (int j = 0; j < iSet[i].size(); j++) {
				assert j == 0 || iSet[i].get(j) > iSet[i].get(j - 1);
			}
		}
		for (int i = 0; i < numStates; i++) {
			for (int j = 0; j < cSet[i].size(); j++) {
				assert j == 0 || cSet[i].get(j) > cSet[i].get(j - 1);
			}
		}
		for (int i = 0; i < numStates; i++) {
			for (int j = 0; j < rSet[i].size(); j++) {
				assert j == 0 || rSet[i].get(j) > rSet[i].get(j - 1);
			}
		}
		for (int i = 0; i < numStates; i++) {
			for (int j = 0; j < rTop[i].size(); j++) {
				assert j == 0 || rTop[i].get(j) > rTop[i].get(j - 1);
			}
		}
		for (int i = 0; i < numStates; i++) {
			for (int j = 0; j < hSet[i].size(); j++) {
				assert j == 0 || hSet[i].get(j) > hSet[i].get(j - 1);
			}
		}

		// group rTrans by src and sym
		final HashMap<SrcSym, ArrayList<RTrans>> bySrcSym = new HashMap<SrcSym, ArrayList<RTrans>>();

		for (final RTrans x : rTrans) {
			final SrcSym srcsym = new SrcSym(x.mSrc, x.mSym);
			ArrayList<RTrans> a = bySrcSym.get(srcsym);
			if (a == null) {
				a = new ArrayList<RTrans>();
				bySrcSym.put(srcsym, a);
			}
			a.add(x);
		}

		checkTimeout(services);

		/*
		 * GENERATE CLAUSES
		 *
		 */

		final EqVarCalc calc = new EqVarCalc(numStates);
		final Horn3ArrayBuilder builder = new Horn3ArrayBuilder(calc.getNumEqVars());

		for (int i = 0; i < numStates; i++) {
			final int eq1 = calc.eqVar(i, i);
			builder.addClauseTrue(eq1);
		}

		for (int i = 0; i < numStates; i++) {
			checkTimeout(services);

			for (int j = i + 1; j < numStates; j++) {
				if (isFinal[i] != isFinal[j]) {
					final int eq1 = calc.eqVar(i, j);
					builder.addClauseFalse(eq1);
				}
			}
		}

		for (int i = 0; i < numStates; i++) {
			checkTimeout(services);

			for (int j = i; j < numStates; j++) {
				final int eq1 = calc.eqVar(i, j);

				if (builder.isAlreadyFalse(eq1)) {
					continue;
				}

				if (!iSet[i].equals(iSet[j]) || !cSet[i].equals(cSet[j])) {
					builder.addClauseFalse(eq1);
				} else {
					// rule 1
					for (int x = 0, y = 0; x < iTransOut.get(i).size() && y < iTransOut.get(j).size();) {
						final ITrans t1 = iTransOut.get(i).get(x);
						final ITrans t2 = iTransOut.get(j).get(y);
						if (t1.mSym < t2.mSym) {
							x++;
						} else if (t1.mSym > t2.mSym) {
							y++;
						} else {
							final int eq2 = calc.eqVar(t1.mDst, t2.mDst);
							builder.addClauseFalseTrue(eq1, eq2);
							x++;
							y++;
						}
					}
					// rule 2
					for (int x = 0, y = 0; x < cTransOut.get(i).size() && y < cTransOut.get(j).size();) {
						final CTrans t1 = cTransOut.get(i).get(x);
						final CTrans t2 = cTransOut.get(j).get(y);
						if (t1.mSym < t2.mSym) {
							x++;
						} else if (t1.mSym > t2.mSym) {
							y++;
						} else {
							final int eq2 = calc.eqVar(t1.mDst, t2.mDst);
							builder.addClauseFalseTrue(eq1, eq2);
							x++;
							y++;
						}
					}
				}
				// rule 3
				for (final int k : rTop[i]) {
					for (final int l : hSet[j]) {
						final int eq2 = calc.eqVar(k, l);
						builder.addClauseFalseFalse(eq1, eq2);
					}
				}
				for (final int k : hSet[i]) {
					for (final int l : rTop[j]) {
						final int eq2 = calc.eqVar(k, l);
						builder.addClauseFalseFalse(eq1, eq2);
					}
				}
				for (final int s1 : rSet[i]) {
					for (final int s2 : rSet[j]) {
						for (final RTrans t1 : bySrcSym.get(new SrcSym(i, s1))) {
							for (final RTrans t2 : bySrcSym.get(new SrcSym(j, s2))) {
								final int eq2 = calc.eqVar(t1.mTop, t2.mTop);
								final int eq3 = calc.eqVar(t1.mDst, t2.mDst);
								builder.addClauseFalseFalseTrue(eq1, eq2, eq3);
							}
						}
					}
				}
			}
		}

		/*
		 * Transitivity clauses
		 *
		 * The naive way is visiting all or almost all clauses. This needs
		 * O(n^3) time.
		 *
		 * Instead we precompute an index of the state pairings that are not
		 * (yet) known to be unmergeable. The other pairings need not be
		 * visited.
		 */

		final IntArray[] possible = new IntArray[numStates];

		for (int i = 0; i < numStates; i++) {
			possible[i] = new IntArray();
		}

		for (int i = 0; i < numStates; i++) {
			checkTimeout(services);

			for (int j = 0; j < numStates; j++) {
				if (!builder.isAlreadyFalse(calc.eqVar(i, j))) {
					possible[i].add(j);
				}
			}
		}

		for (int i = 0; i < numStates; i++) {
			checkTimeout(services);

			for (final int j : possible[i]) {
				final int eq1 = calc.eqVar(i, j);
				for (final int k : possible[j]) {
					final int eq2 = calc.eqVar(j, k);
					final int eq3 = calc.eqVar(i, k);
					builder.addClauseFalseFalseTrue(eq1, eq2, eq3);
				}
			}
		}

		final Horn3Array clauses = builder.extract();
		return clauses;
	}

	private static void checkTimeout(final AutomataLibraryServices services) throws AutomataOperationCanceledException {
		if (!services.getProgressAwareTimer().continueProcessing()) {
			throw new AutomataOperationCanceledException(Generator.class);
		}
	}

	/**
	 * This encapsulates some evil intricate knowledge about the representation of the equivalence variables as integers
	 */
	private static final class EqVarCalc {
		private final int mN;

		EqVarCalc(final int numStates) {
			mN = numStates;
		}

		int getNumEqVars() {
			// add 2 because 0 and 1 are reserved for const false / const true
			return 2 + mN * (mN + 1) / 2;
		}

		int eqVar(final int a, final int b) {
			assert 0 <= a && a < mN;
			assert 0 <= b && b < mN;
			if (a > b) {
				return eqVar(b, a);
			}
			// add 2 because 0 and 1 are reserved for const false / const true
			return 2 + (mN * (mN + 1) / 2) - ((mN - a) * (mN - a + 1) / 2) + b - a;
		}
	}

	private static final class SrcSym {
		private final int mSrc;
		private final int mSym;

		SrcSym(final int src, final int sym) {
			mSrc = src;
			mSym = sym;
		}

		@Override
		public boolean equals(final Object obj) {
			if (obj == null || !(obj instanceof SrcSym)) {
				return false;
			}

			final SrcSym b = (SrcSym) obj;

			return mSrc == b.mSrc && mSym == b.mSym;
		}

		@Override
		public int hashCode() {
			return mSrc * 31 + mSym;
		}
	}
}
