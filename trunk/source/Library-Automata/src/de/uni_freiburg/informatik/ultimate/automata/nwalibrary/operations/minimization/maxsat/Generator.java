/*
 * Copyright (C) 2016 Jens Stimpfle <stimpflj@informatik.uni-freiburg.de>

 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.maxsat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;

/**
 * Formulate "merge relation constraints" (as defined in my thesis) as a
 * MAX-SAT instance.
 *
 * A solution to the instance can be converted to a merge relation later.
 *
 * @author stimpflj
 */
final class Generator {

	/**
	 * Convert a solved instance to a merge relation
	 */
	static Partition makeMergeRelation(int numStates, char[] assigned) {
		UnionFind unionFind = new UnionFind(numStates);
		EqVarCalc calc = new EqVarCalc(numStates);

		assert assigned.length == calc.getNumEqVars();

		for (int x : assigned)
			assert x == Solver.TRUE || x == Solver.FALSE;

		for (int i = 0; i < numStates; i++) {
			for (int j = i+1; j < numStates; j++) {
				int eqVar = calc.eqVar(i, j);
				if (assigned[eqVar] == Solver.TRUE) {
					unionFind.merge(i, j);
				}
			}
		}

		return Partition.compress(unionFind.extractRoots());
	}

	/**
	 * @param inNWA
	 *            input NWA.
	 *
	 * @param history
	 *            precalculated history states for <code>inNWA</code>.
	 *
	 * @return A (consistent) Partition which represents the minimized
	 *         automaton.
	 */
	static Horn3Array generateClauses(NWA inNWA, ArrayList<Hist> history) {
		assert Hist.checkConsistency(inNWA, history);

		// "assert" that there are no transitions which are never taken
		{
			HashSet<Hist> hs = new HashSet<Hist>();
			for (Hist h : history)
				hs.add(h);
			for (RTrans x : inNWA.rTrans)
				assert hs.contains(new Hist(x.src, x.top));
		}

		// some "namespace imports"
		int numStates = inNWA.numStates;
		//@SuppressWarnings("unused") int numISyms = inNWA.numISyms;
		//@SuppressWarnings("unused") int numCSyms = inNWA.numCSyms;
		//@SuppressWarnings("unused") int numRSyms = inNWA.numRSyms;
		//@SuppressWarnings("unused") boolean[] isInitial = inNWA.isInitial;
		boolean[] isFinal = inNWA.isFinal;
		int numITrans = inNWA.iTrans.length;
		int numCTrans = inNWA.cTrans.length;
		int numRTrans = inNWA.rTrans.length;
		ITrans[] iTrans = inNWA.iTrans.clone();
		CTrans[] cTrans = inNWA.cTrans.clone();
		RTrans[] rTrans = inNWA.rTrans.clone();
		RTrans[] rTransTop = inNWA.rTrans.clone();

		history = new ArrayList<Hist>(history);

		// IMPORTANT. Sort inputs
		Arrays.sort(iTrans, ITrans::compareSrcSymDst);
		Arrays.sort(cTrans, CTrans::compareSrcSymDst);
		Arrays.sort(rTrans, RTrans::compareSrcSymTopDst);
		Arrays.sort(rTransTop, RTrans::compareSrcTopSymDst);

		history.sort(Hist::compareLinHier);

		// All "outgoing" transitions, grouped by src, then sorted by (top), sym, dst
		ArrayList<ArrayList<ITrans>> iTransOut = new ArrayList<ArrayList<ITrans>>();
		ArrayList<ArrayList<CTrans>> cTransOut = new ArrayList<ArrayList<CTrans>>();
		ArrayList<ArrayList<RTrans>> rTransOut = new ArrayList<ArrayList<RTrans>>();

		for (int i = 0; i < numStates; i++) iTransOut.add(new ArrayList<ITrans>());
		for (int i = 0; i < numStates; i++) cTransOut.add(new ArrayList<CTrans>());
		for (int i = 0; i < numStates; i++) rTransOut.add(new ArrayList<RTrans>());

		for (int i = 0; i < numITrans; i++) iTransOut.get(iTrans[i].src).add(iTrans[i]);
		for (int i = 0; i < numCTrans; i++) cTransOut.get(cTrans[i].src).add(cTrans[i]);
		for (int i = 0; i < numRTrans; i++) rTransOut.get(rTrans[i].src).add(rTrans[i]);

		IntArray[] iSet = new IntArray[numStates];
		IntArray[] cSet = new IntArray[numStates];
		IntArray[] rSet = new IntArray[numStates];
		IntArray[] rTop = new IntArray[numStates];
		IntArray[] hSet = new IntArray[numStates];

		for (int i = 0; i < numStates; i++) iSet[i] = new IntArray();
		for (int i = 0; i < numStates; i++) cSet[i] = new IntArray();
		for (int i = 0; i < numStates; i++) rSet[i] = new IntArray();
		for (int i = 0; i < numStates; i++) rTop[i] = new IntArray();
		for (int i = 0; i < numStates; i++) hSet[i] = new IntArray();

		for (int i = 0; i < numITrans; i++)	if (i == 0 || iTrans[i-1].src != iTrans[i].src || iTrans[i-1].sym != iTrans[i].sym) iSet[iTrans[i].src].add(iTrans[i].sym);
		for (int i = 0; i < numCTrans; i++)	if (i == 0 || cTrans[i-1].src != cTrans[i].src || cTrans[i-1].sym != cTrans[i].sym) cSet[cTrans[i].src].add(cTrans[i].sym);
		for (int i = 0; i < numRTrans; i++)	if (i == 0 || rTrans[i-1].src != rTrans[i].src || rTrans[i-1].sym != rTrans[i].sym) rSet[rTrans[i].src].add(rTrans[i].sym);
		for (int i = 0; i < numRTrans; i++)	if (i == 0 || rTransTop[i-1].src != rTransTop[i].src || rTransTop[i-1].top != rTransTop[i].top) rTop[rTransTop[i].src].add(rTransTop[i].top);

		{
			// make the hSet, i.e. those history states except bottom-of-stack
			// symbol which are not in the outgoing return transitions as
			// top-of-stack symbol.
			int i = 0;
			for (Hist h : history) {
				for (; i < numRTrans; i++)
					if (h.lin < rTransTop[i].src
							|| (h.lin == rTransTop[i].src && h.hier <= rTransTop[i].top))
						break;
				if (i == numRTrans
						|| h.lin < rTransTop[i].src
						|| (h.lin == rTransTop[i].src && h.hier < rTransTop[i].top))
					if (h.hier >= 0) // could be bottom-of-stack (-1)
						hSet[h.lin].add(h.hier);
			}
		}

		for (int i = 0; i < numStates; i++) for (int j = 0; j < iSet[i].size(); j++) assert j == 0 || iSet[i].get(j) > iSet[i].get(j-1);
		for (int i = 0; i < numStates; i++) for (int j = 0; j < cSet[i].size(); j++) assert j == 0 || cSet[i].get(j) > cSet[i].get(j-1);
		for (int i = 0; i < numStates; i++) for (int j = 0; j < rSet[i].size(); j++) assert j == 0 || rSet[i].get(j) > rSet[i].get(j-1);
		for (int i = 0; i < numStates; i++) for (int j = 0; j < rTop[i].size(); j++) assert j == 0 || rTop[i].get(j) > rTop[i].get(j-1);
		for (int i = 0; i < numStates; i++) for (int j = 0; j < hSet[i].size(); j++) assert j == 0 || hSet[i].get(j) > hSet[i].get(j-1);

		// group rTrans by src and sym
		HashMap<SrcSym, ArrayList<RTrans>> bySrcSym = new HashMap<SrcSym, ArrayList<RTrans>>();

		for (RTrans x : rTrans) {
			SrcSym srcsym = new SrcSym(x.src, x.sym);
			ArrayList<RTrans> a = bySrcSym.get(srcsym);
			if (a == null) {
				a = new ArrayList<RTrans>();
				bySrcSym.put(srcsym, a);
			}
			a.add(x);
		}


		/*
		 * GENERATE CLAUSES
		 *
		 */

		EqVarCalc calc = new EqVarCalc(numStates);
		Horn3ArrayBuilder builder = new Horn3ArrayBuilder(calc.getNumEqVars());

		for (int i = 0; i < numStates; i++) {
			int eq1 = calc.eqVar(i, i);
			builder.addClauseT(eq1);
		}

		for (int i = 0; i < numStates; i++) {
			for (int j = i+1; j < numStates; j++) {
				if (isFinal[i] != isFinal[j]) {
					int eq1 = calc.eqVar(i, j);
					builder.addClauseF(eq1);
				}
			}
		}

		for (int i = 0; i < numStates; i++) {
			for (int j = i; j < numStates; j++) {
				int eq1 = calc.eqVar(i, j);

				if (builder.isAlreadyFalse(eq1))
					continue;

				if (!iSet[i].equals(iSet[j]) || !cSet[i].equals(cSet[j])) {
					builder.addClauseF(eq1);
				} else {
					// rule 1
					for (int x = 0, y = 0; x < iTransOut.get(i).size() && y < iTransOut.get(j).size();) {
						ITrans t1 = iTransOut.get(i).get(x);
						ITrans t2 = iTransOut.get(j).get(y);
						if (t1.sym < t2.sym) {
							x++;
						} else if (t1.sym > t2.sym) {
							y++;
						} else {
							int eq2 = calc.eqVar(t1.dst, t2.dst);
							builder.addClauseFT(eq1, eq2);
							x++;
							y++;
						}
					}
					// rule 2
					for (int x = 0, y = 0; x < cTransOut.get(i).size() && y < cTransOut.get(j).size();) {
						CTrans t1 = cTransOut.get(i).get(x);
						CTrans t2 = cTransOut.get(j).get(y);
						if (t1.sym < t2.sym) {
							x++;
						} else if (t1.sym > t2.sym) {
							y++;
						} else {
							int eq2 = calc.eqVar(t1.dst, t2.dst);
							builder.addClauseFT(eq1, eq2);
							x++;
							y++;
						}
					}
				}
				// rule 3
				for (int k : rTop[i]) {
					for (int l : hSet[j]) {
						int eq2 = calc.eqVar(k, l);
						builder.addClauseFF(eq1, eq2);
					}
				}
				for (int k : hSet[i]) {
					for (int l : rTop[j]) {
						int eq2 = calc.eqVar(k, l);
						builder.addClauseFF(eq1, eq2);
					}
				}
				for (int s1 : rSet[i]) {
					for (int s2 : rSet[j]) {
						for (RTrans t1 : bySrcSym.get(new SrcSym(i, s1))) {
							for (RTrans t2 : bySrcSym.get(new SrcSym(j, s2))) {
								int eq2 = calc.eqVar(t1.top, t2.top);
								int eq3 = calc.eqVar(t1.dst, t2.dst);
								builder.addClauseFFT(eq1, eq2, eq3);
							}
						}
					}
				}
			}
		}

		for (int i = 0; i < numStates; i++) {
			for (int j = i+1; j < numStates; j++) {
				int eq1 = calc.eqVar(i, j);

				for (int k = j+1; k < numStates; k++) {
					int eq2 = calc.eqVar(j, k);
					int eq3 = calc.eqVar(i, k);
					builder.addClauseFFT(eq1, eq2, eq3);
					builder.addClauseFFT(eq2, eq3, eq1);
					builder.addClauseFFT(eq3, eq1, eq2);
				}
			}
		}

		Horn3Array clauses = builder.extract();
		return clauses;
	}

	/**
	 * This encapsulates some evil intricate knowledge about the
	 * representation of the equivalence variables as integers
	 */
	private static final class EqVarCalc {
		private final int n;

		EqVarCalc(int numStates) {
			this.n = numStates;
		}

		int getNumEqVars() {
			// add 2 because 0 and 1 are reserved for const false / const true
			return 2 + n*(n+1)/2;
		}

		int eqVar(int a, int b) {
			assert 0 <= a && a < n;
			assert 0 <= b && b < n;
			if (a > b) return eqVar(b, a);
			// add 2 because 0 and 1 are reserved for const false / const true
			return 2 + (n*(n+1)/2)-((n-a)*(n-a+1)/2) + b-a;
		}
	}

	private static final class SrcSym {
		private final int src;
		private final int sym;

		SrcSym(int src, int sym) {
			this.src = src;
			this.sym = sym;
		}

		@Override
		public boolean equals(Object obj) {
			if (obj == null || !(obj instanceof SrcSym))
				return false;

			SrcSym b = (SrcSym) obj;

			return src == b.src && sym == b.sym;
		}

		@Override
		public int hashCode() {
			return src * 31 + sym;
		}
	}
}
