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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;

/**
 * Minimize an NWA by converting a sufficient set of logical conditions
 * for state equivalency to Horn clauses and solve them as a (MAX)SAT problem.
 *
 * This is currently not practical since state equivalency needs to be
 * transitive and we need numStates^3 clauses for transitivity.
 *
 * @author stimpflj
 */
public class MinimizeNwaMaxSATReal {

	/**
	 * @param inNWA input NWA. The NWA is mutated (transitions sorted).
	 *        Give me a copy instead if mutation isn't possible for you.
	 * @param precalculated history states for <code>inNWA</code>.
	 *        For each state, a sorted list of its history states.
	 *
	 * @return A (consistent) NiceClasses which represents
	 *         the minimized automaton.
	 */
	public static NiceClasses minimize(NiceNWA inNWA, NiceHist[] history) {
		assert NiceHist.checkHistoryStatesConsistency(inNWA, history);
		// this assertion is needed for "rule 3". probably makes sense to add
		// to the consistency checking for history sets
		{
			HashSet<NiceHist> hs = new HashSet<NiceHist>();
			for (NiceHist h : history)
				hs.add(h);
			for (NiceRTrans x : inNWA.rTrans)
				assert hs.contains(new NiceHist(x.src, x.top));
		}

		// some "imports"
		int numStates = inNWA.numStates;
		@SuppressWarnings("unused") int numISyms = inNWA.numISyms;
		@SuppressWarnings("unused") int numCSyms = inNWA.numCSyms;
		int numRSyms = inNWA.numRSyms;
		int numITrans = inNWA.iTrans.length;
		int numCTrans = inNWA.cTrans.length;
		int numRTrans = inNWA.rTrans.length;
		@SuppressWarnings("unused") boolean[] isInitial = inNWA.isInitial;
		boolean[] isFinal = inNWA.isFinal;
		NiceITrans[] iTrans = inNWA.iTrans;
		NiceCTrans[] cTrans = inNWA.cTrans;
		NiceRTrans[] rTrans = inNWA.rTrans;

		// accumulate clauses to be solved by SAT solver
		ArrayList<HornClause3> clauses = new ArrayList<HornClause3>();
		EqVarCalc calc = new EqVarCalc(numStates);

		/*
		 *
		 * RULE 1:
		 * Create clauses: NOT(src1 ~ src2) OR (dst1 ~ dst2)
		 * for all src1, src2, dst1, dst2
		 * described by the following query:
		 *
		 * SELECT
		 *         src1, src2, dst1, dst2
		 * FROM
		 *         (SELECT
		 *                 A.src AS src1, A.sym AS sym1, A.dst AS dst1,
		 *                 B.src AS src2, B.sym AS sym2, B.dst AS dst2
		 *         FROM
		 *                 iTrans A, iTrans B
		 *         WHERE
		 *                 (src1, src2) IN HaveSameSetOfOutgoingInternalSymbols
		 *           AND
		 *                 sym1 == sym2)
		 *
		 * RULE 2:
		 * Create clauses: NOT(Eq(src1, src2)) OR Eq(dst1,dst2)
		 * for all src1, src2, dst1, dst2
		 * described by the following query:
		 *
		 * SELECT
		 *         src1, src2, dst1, dst2
		 * FROM
		 *         (SELECT
		 *                 A.src AS src1, A.sym AS sym1, A.dst AS dst1,
		 *                 B.src AS src2, B.sym AS sym2, B.dst AS dst2,
		 *         FROM
		 *                 cTrans A, cTrans B
		 *         WHERE
		 *                 (src1, src2) IN HaveSameSetOfOutgoingCallSymbols
		 *           AND
		 *                 sym1 == sym2)
		 *
		 * RULE 3:
		 * Create clauses: NOT(Eq(src1, src2)) OR NOT(Eq(top1, top2)) OR Eq(dst1, dst2)
		 * for all src1, src2, top1, top2, dst1, dst2
		 * described by the following query:
		 *
		 * SELECT
		 *         src1, src2, top1, top2, dst1, dst2
		 * FROM
		 *         (SELECT
		 *                 A.src AS src1, A.top AS top1, A.sym AS sym1, A.dst AS dst1,
		 *                 B.src AS src2, B.top as top2, B.sym AS sym2, B.dst AS dst2
		 *         FROM
		 *                 rTrans A, rTrans B
		 *         WHERE
		 *                 (src1, src2) IN HaveSameSetOfOutgoingReturnSymbols
		 *           AND
		 *                 sym1 == sym2)
		 */

		Arrays.sort(iTrans, NiceITrans::compareSrcSymDst);
		Arrays.sort(cTrans, NiceCTrans::compareSrcSymDst);
		Arrays.sort(rTrans, NiceRTrans::compareSrcSymTopDst);

		// All outgoing edges, sorted by src, sym, (top), dst just like above
		ArrayList<ArrayList<NiceITrans>> iTransOut = new ArrayList<ArrayList<NiceITrans>>();
		ArrayList<ArrayList<NiceCTrans>> cTransOut = new ArrayList<ArrayList<NiceCTrans>>();
		ArrayList<ArrayList<NiceRTrans>> rTransOut = new ArrayList<ArrayList<NiceRTrans>>();

		for (int i = 0; i < numStates; i++) iTransOut.add(new ArrayList<NiceITrans>());
		for (int i = 0; i < numStates; i++) cTransOut.add(new ArrayList<NiceCTrans>());
		for (int i = 0; i < numStates; i++) rTransOut.add(new ArrayList<NiceRTrans>());

		for (int i = 0; i < numITrans; i++) iTransOut.get(iTrans[i].src).add(iTrans[i]);
		for (int i = 0; i < numCTrans; i++) cTransOut.get(cTrans[i].src).add(cTrans[i]);
		for (int i = 0; i < numRTrans; i++) rTransOut.get(rTrans[i].src).add(rTrans[i]);

		// strictly ascending lists of outgoing symbols, per source state
		ArrayList<ArrayList<Integer>> iSyms = new ArrayList<ArrayList<Integer>>();
		ArrayList<ArrayList<Integer>> cSyms = new ArrayList<ArrayList<Integer>>();
		ArrayList<ArrayList<Integer>> rSyms = new ArrayList<ArrayList<Integer>>();

		for (int i = 0; i < numStates; i++) iSyms.add(new ArrayList<Integer>());
		for (int i = 0; i < numStates; i++) cSyms.add(new ArrayList<Integer>());
		for (int i = 0; i < numStates; i++) rSyms.add(new ArrayList<Integer>());

		for (int i = 0; i < numITrans; i++)	if (i == 0 || (iTrans[i-1].src == iTrans[i].src && iTrans[i-1].sym != iTrans[i].sym)) iSyms.get(iTrans[i].src).add(iTrans[i].sym);
		for (int i = 0; i < numCTrans; i++)	if (i == 0 || (cTrans[i-1].src == cTrans[i].src && cTrans[i-1].sym != cTrans[i].sym)) cSyms.get(cTrans[i].src).add(cTrans[i].sym);
		for (int i = 0; i < numRTrans; i++)	if (i == 0 || (rTrans[i-1].src == rTrans[i].src && rTrans[i-1].sym != rTrans[i].sym)) rSyms.get(rTrans[i].src).add(rTrans[i].sym);

		// set of outgoing symbols -> states with that set
		HashMap<ArrayList<Integer>, ArrayList<Integer>> statesByISyms = new HashMap<ArrayList<Integer>, ArrayList<Integer>>();
		HashMap<ArrayList<Integer>, ArrayList<Integer>> statesByCSyms = new HashMap<ArrayList<Integer>, ArrayList<Integer>>();
		HashMap<ArrayList<Integer>, ArrayList<Integer>> statesByRSyms = new HashMap<ArrayList<Integer>, ArrayList<Integer>>();

		// state -> some state representing the equivalence class of all states with same set of outgoing symbols
		int[] iSymRepr = new int[numStates];
		int[] cSymRepr = new int[numStates];
		int[] rSymRepr = new int[numStates];

		for (int i = 0; i < numStates; i++) { ArrayList<Integer> k = iSyms.get(i); ArrayList<Integer> v = statesByISyms.get(k); if (v == null) { v = new ArrayList<Integer>(); statesByISyms.put(k, v); } v.add(i); iSymRepr[i] = v.get(0); }
		for (int i = 0; i < numStates; i++) { ArrayList<Integer> k = cSyms.get(i); ArrayList<Integer> v = statesByCSyms.get(k); if (v == null) { v = new ArrayList<Integer>(); statesByCSyms.put(k, v); } v.add(i); cSymRepr[i] = v.get(0); }
		for (int i = 0; i < numStates; i++) { ArrayList<Integer> k = rSyms.get(i); ArrayList<Integer> v = statesByRSyms.get(k); if (v == null) { v = new ArrayList<Integer>(); statesByRSyms.put(k, v); } v.add(i); rSymRepr[i] = v.get(0); }

		// emit clauses for reflexivity
		for (int i = 0; i < numStates; i++) {
			int eqVar = calc.eqVar(i, i);
			clauses.add(HornClause3.T(eqVar));
		}

		// we don't need to emit clauses for symmetricity since we identify i~j with j~i in EqVarCalc

		// emit clauses for transitivity
		// NOTE: this is super expensive and the most likely opportunity for optimization
		for (int i = 0; i < numStates; i++) {
			for (int j = i+1; j < numStates; j++) {
				int eq1 = calc.eqVar(i, j);
				for (int k = j+1; k < numStates; k++) {
					int eq2 = calc.eqVar(j, k);
					int eq3 = calc.eqVar(i, k);
					clauses.add(HornClause3.FFT(eq1, eq2, eq3));
				}
			}
		}

		// emit clauses for rule 0 (to separate final and nonfinal states)
		for (int i = 0; i < numStates; i++)
			for (int j = i+1; j < numStates; j++)
				if (isFinal[i] != isFinal[j])
					clauses.add(HornClause3.F(calc.eqVar(i, j)));

		// optimization: avoid emitting clauses from rule 1 and rule 2
		// if iSym or cSym sets are not equal
		for (int i = 0; i < numStates; i++) {
			for (int j = 0; j < numStates; j++) {
				int eqVar = calc.eqVar(i, j);
				if (iSymRepr[i] != iSymRepr[j] ||
					cSymRepr[i] != cSymRepr[j]) {
					/* If the outgoing symbol sets are not equal
					 * we don't consider merging. This is because we
					 * assume that every outgoing edge can lead to
					 * an accepting state. If that shouldn't be the
					 * case that this optimization is still not unsound.
					 * We only miss an opportunity for merging.
					 */
					clauses.add(HornClause3.F(eqVar));
				}
			}
		}

		// emit clauses from rule 1
		for (int i = 0; i < numStates; i++) {
			for (int j = i+1; j < numStates; j++) {
				int eqVarSrc = calc.eqVar(i, j);
				if (iSymRepr[i] != iSymRepr[j] || cSymRepr[i] != cSymRepr[j]) {
					// see optimization above
				} else {
					// NOTE: this is inefficient when there are many out-edges
					for (NiceITrans x : iTransOut.get(i)) {
						for (NiceITrans y : iTransOut.get(j)) {
							if (x.sym == y.sym) {
								int eqVarDst = calc.eqVar(x.dst, y.dst);
								clauses.add(HornClause3.FT(eqVarSrc, eqVarDst));
							}
						}
					}
				}
			}
		}

		// emit clauses from rule 2
		for (int i = 0; i < numStates; i++) {
			for (int j = i+1; j < numStates; j++) {
				int eqVarSrc = calc.eqVar(i, j);
				if (iSymRepr[i] != iSymRepr[j] || cSymRepr[i] != cSymRepr[j]) {
					// see optimization above
				} else {
					// NOTE: this is inefficient when there are many out-edges
					for (NiceCTrans x : cTransOut.get(i)) {
						for (NiceCTrans y : cTransOut.get(j)) {
							if (x.sym == y.sym) {
								int eqVarDst = calc.eqVar(x.dst, y.dst);
								clauses.add(HornClause3.FT(eqVarSrc, eqVarDst));
							}
						}
					}
				}
			}
		}

		// emit clauses from rule 3
		{
			// TODO: Not at all sure if this is correct

			// "group by return symbol"
			ArrayList<ArrayList<NiceRTrans>> groups = new ArrayList<ArrayList<NiceRTrans>>();
			for (int i = 0; i < numRSyms; i++)
				groups.add(new ArrayList<NiceRTrans>());
			for (NiceRTrans x : rTrans)
				groups.get(x.sym).add(x);
			for (ArrayList<NiceRTrans> g : groups) {
				for (int i = 0; i < g.size(); i++) {
					for (int j = i+1; j < g.size(); j++) {
						NiceRTrans x = g.get(i);
						NiceRTrans y = g.get(j);
						int v0 = calc.eqVar(x.src, y.src);
						int v1 = calc.eqVar(x.top, y.top);
						int v2 = calc.eqVar(x.dst, y.dst);
						clauses.add(HornClause3.FFT(v0, v1, v2));
					}
				}
			}
		}

		HornClause3[] clArray = clauses.toArray(new HornClause3[clauses.size()]);
		Assign[] assigned = new MaxSATSolve(calc.getNumEqVars(), clArray).solve();

		if (assigned == null) {
			System.err.println("could not solve");
			return null;
		}

		/*
		System.err.printf("Assignments (%d states, %d variables):", numStates, calc.getNumEqVars());
		for (int i = 0; i < numStates; i++) {
			for (int j = i+1; j < numStates; j++) {
				int eqVar = calc.eqVar(i,  j);
				assert assigned[eqVar] != Assign.NONE;
				String maybeNot = assigned[eqVar] == Assign.FALSE ? "NOT" : "";
				System.err.printf(" %s(%d~%d)", maybeNot, i, j);
			}
		}
		System.err.printf("\n");
		System.err.flush();
		*/

		NiceUnionFind unionFind = new NiceUnionFind(numStates);
		for (int i = 0; i < numStates; i++) {
			for (int j = i+1; j < numStates; j++) {
				int eqVar = calc.eqVar(i, j);
				if (assigned[eqVar] == Assign.TRUE)
					unionFind.merge(i, j);
			}
		}

		return NiceClasses.compress(unionFind.getRoots());
	}

	/** Test the thing */
	public static void main(String[] args) throws FileNotFoundException, IOException {
		OutputStreamWriter out = new OutputStreamWriter(System.err);
		NiceNWA nwa = NiceScan.inputAsRelations("/tmp/test2.nwa");
		assert nwa != null;

		// history states algorithm not implemented :-(
		NiceHist[] dummy = new NiceHist[0];

		NicePrint.printNWA(out, nwa);
		NiceClasses eq = minimize(nwa, dummy);
		NicePrint.printClasses(out, eq);
	}
}

class EqVarCalc {
	private final int numStates;

	public EqVarCalc(int numStates) {
		this.numStates = numStates;
	}

	public int eqVar(int a, int b) {
		assert 0 <= a && a < numStates;
		assert 0 <= b && b < numStates;
		if (a > b) return eqVar(b, a);
		int n = numStates;
		// add 2 because 0 and 1 are reserved for const false / const true
		return 2 + (n*(n+1)/2)-((n-a)*(n-a+1)/2) + b-a;
	}

	public int getNumEqVars() {
		// add 2 because 0 and 1 are reserved for const false / const true
		return 2 + numStates*(numStates+1)/2;
	}
}
