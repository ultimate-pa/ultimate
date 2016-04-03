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
 * This is currently not practical since state equivalency needs to be
 * transitive and we need numStates^3 clauses for transitivity.
 *
 * @author stimpflj
 */
public class ClausesGenerator {

	/**
	 * Convert a solved instance to a merge relation
	 */
	public static EqCls makeMergeRelation(int numStates, Assign[] assignments) {
		EqVarCalc calc = new EqVarCalc(numStates);

		assert assignments.length == calc.getNumEqVars();
		for (Assign x : assignments)
			assert x == Assign.TRUE || x == Assign.FALSE;

		UnionFind unionFind = new UnionFind(numStates);
		for (int i = 0; i < numStates; i++) {
			for (int j = i+1; j < numStates; j++) {
				int eqVar = calc.eqVar(i, j);
				if (assignments[eqVar] == Assign.TRUE) {
					unionFind.merge(i, j);
				}
			}
		}

		return EqCls.compress(unionFind.getRoots());
	}

	/**
	 * @param inNWA input NWA.
	 *
	 * @param history precalculated history states for <code>inNWA</code>.
	 *
	 * @return A (consistent) EqCls which represents the
	 * minimized automaton.
	 */
	public static ArrayList<HornClause3> generateConstraints(NWA inNWA, ArrayList<Hist> history) {
		assert Hist.checkHistoryStatesConsistency(inNWA, history);
		{
			// "assert" that there are no transitions which are never taken
			HashSet<Hist> hs = new HashSet<Hist>();
			for (Hist h : history)
				hs.add(h);
			for (RTrans x : inNWA.rTrans) {
				if (!hs.contains(new Hist(x.src, x.top)))
					System.err.printf("missing %d %d\n",  x.src, x.top);
				assert hs.contains(new Hist(x.src, x.top));
			}
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

		ArrayList<ArrayList<Integer>> iSet = new ArrayList<ArrayList<Integer>>();
		ArrayList<ArrayList<Integer>> cSet = new ArrayList<ArrayList<Integer>>();
		ArrayList<ArrayList<Integer>> rSet = new ArrayList<ArrayList<Integer>>();
		ArrayList<ArrayList<Integer>> rTop = new ArrayList<ArrayList<Integer>>();
		ArrayList<ArrayList<Integer>> hSet = new ArrayList<ArrayList<Integer>>();

		for (int i = 0; i < numStates; i++) iSet.add(new ArrayList<Integer>());
		for (int i = 0; i < numStates; i++) cSet.add(new ArrayList<Integer>());
		for (int i = 0; i < numStates; i++) rSet.add(new ArrayList<Integer>());
		for (int i = 0; i < numStates; i++) rTop.add(new ArrayList<Integer>());
		for (int i = 0; i < numStates; i++) hSet.add(new ArrayList<Integer>());

		for (int i = 0; i < numITrans; i++)	if (i == 0 || iTrans[i-1].src != iTrans[i].src || iTrans[i-1].sym != iTrans[i].sym) iSet.get(iTrans[i].src).add(iTrans[i].sym);
		for (int i = 0; i < numCTrans; i++)	if (i == 0 || cTrans[i-1].src != cTrans[i].src || cTrans[i-1].sym != cTrans[i].sym) cSet.get(cTrans[i].src).add(cTrans[i].sym);
		for (int i = 0; i < numRTrans; i++)	if (i == 0 || rTrans[i-1].src != rTrans[i].src || rTrans[i-1].sym != rTrans[i].sym) rSet.get(rTrans[i].src).add(rTrans[i].sym);
		for (int i = 0; i < numRTrans; i++)	if (i == 0 || rTransTop[i-1].src != rTransTop[i].src || rTransTop[i-1].top != rTransTop[i].top) rTop.get(rTransTop[i].src).add(rTransTop[i].top);

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
						hSet.get(h.lin).add(h.hier);
			}
		}

		for (int i = 0; i < numStates; i++) for (int j = 0; j < iSet.get(i).size(); j++) assert j == 0 || iSet.get(i).get(j) > iSet.get(i).get(j-1);
		for (int i = 0; i < numStates; i++) for (int j = 0; j < cSet.get(i).size(); j++) assert j == 0 || cSet.get(i).get(j) > cSet.get(i).get(j-1);
		for (int i = 0; i < numStates; i++) for (int j = 0; j < rSet.get(i).size(); j++) assert j == 0 || rSet.get(i).get(j) > rSet.get(i).get(j-1);
		for (int i = 0; i < numStates; i++) for (int j = 0; j < rTop.get(i).size(); j++) assert j == 0 || rTop.get(i).get(j) > rTop.get(i).get(j-1);
		for (int i = 0; i < numStates; i++) for (int j = 0; j < hSet.get(i).size(); j++) assert j == 0 || hSet.get(i).get(j) > hSet.get(i).get(j-1);

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
		HornCNFBuilder builder = new HornCNFBuilder(calc.getNumEqVars());

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
			System.err.printf("now at %d, %d clauses %d requests\n", i, builder.getNumClauses(), builder.getNumRequests());
			for (int j = i; j < numStates; j++) {
				if (!iSet.get(i).equals(iSet.get(j))
						|| !cSet.get(i).equals(cSet.get(j))) {
					int eq1 = calc.eqVar(i, j);
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
							int eq1 = calc.eqVar(t1.src, t2.src);
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
							int eq1 = calc.eqVar(t1.src, t2.src);
							int eq2 = calc.eqVar(t1.dst, t2.dst);
							builder.addClauseFT(eq1, eq2);
							x++;
							y++;
						}
					}
				}
				// rule 3
				for (int k : rTop.get(i)) {
					for (int l : hSet.get(j)) {
						int eq1 = calc.eqVar(i, j);
						int eq2 = calc.eqVar(k, l);
						builder.addClauseFF(eq1, eq2);
					}
				}
				for (int k : hSet.get(i)) {
					for (int l : rTop.get(j)) {
						int eq1 = calc.eqVar(i, j);
						int eq2 = calc.eqVar(k, l);
						builder.addClauseFF(eq1, eq2);
					}
				}
				for (int s1 : rSet.get(i)) {
					for (int s2 : rSet.get(j)) {
						for (RTrans t1 : bySrcSym.get(new SrcSym(i, s1))) {
							for (RTrans t2 : bySrcSym.get(new SrcSym(j, s2))) {
								int eq1 = calc.eqVar(t1.src, t2.src);
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
			System.err.printf("transitive clauses: now at %d, %d clauses, %d requests\n", i, builder.getNumClauses(), builder.getNumRequests());
			for (int j = i+1; j < numStates; j++) {
				for (int k = j+1; k < numStates; k++) {
					int eq1 = calc.eqVar(i, j);
					int eq2 = calc.eqVar(j, k);
					int eq3 = calc.eqVar(i, k);
					builder.addClauseFFT(eq1, eq2, eq3);
					builder.addClauseFFT(eq2, eq3, eq1);
					builder.addClauseFFT(eq3, eq1, eq2);
				}
			}
		}

		/*
		{
			HashMap<Integer, String> name = new HashMap<Integer, String>();
			name.put(0, "F");
			name.put(1, "T");
			for (int i = 0; i < numStates; i++)
				for (int j = i; j < numStates; j++)
					name.put(calc.eqVar(i, j), "X_" + Integer.toString(i) + "," + Integer.toString(j));

			System.err.printf("\nClauses:\n");
			for (HornClause3 x : builder.getClauses()) {
				String s0 =	name.get(x.l0);
				String s1 = name.get(x.l1);
				String s2 = name.get(x.l2);
				System.err.printf("NOT %s OR NOT %s OR %s\n", s0, s1, s2);
			}
		}
		*/

		ArrayList<HornClause3> clauses = builder.getClauses();
		System.err.printf("number of clauses: %d\n", clauses.size());
		System.err.printf("number of clause-add requests: %d\n", builder.getNumRequests());

		return clauses;
	}
}

/**
 * This encapsulates some evil intricate knowledge about the
 * representation of the equivalence variables as integers
 */
class EqVarCalc {
	private int n;

	public EqVarCalc(int numStates) {
		this.n = numStates;
	}

	public int getNumEqVars() {
		// add 2 because 0 and 1 are reserved for const false / const true
		return 2 + n*(n+1)/2;
	}

	public int eqVar(int a, int b) {
		assert 0 <= a && a < n;
		assert 0 <= b && b < n;
		if (a > b) return eqVar(b, a);
		// add 2 because 0 and 1 are reserved for const false / const true
		return 2 + (n*(n+1)/2)-((n-a)*(n-a+1)/2) + b-a;
	}
}

class SrcSym {
	int src;
	int sym;

	public SrcSym(int src, int sym) {
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
