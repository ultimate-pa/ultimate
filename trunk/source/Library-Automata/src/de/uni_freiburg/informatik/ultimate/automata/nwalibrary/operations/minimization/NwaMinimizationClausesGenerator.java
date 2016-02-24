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
public class NwaMinimizationClausesGenerator {

	/**
	 * Convert a solved instance to a merge relation
	 */
	public static NiceClasses makeMergeRelation(int numStates, Assign[] assignments) {
		EqVarCalc calc = new EqVarCalc(numStates);

		assert assignments.length == calc.getNumEqVars();
		for (Assign x : assignments)
			assert x == Assign.TRUE || x == Assign.FALSE;

		/*for (int i : new int[]{16, 29, 41, 49, 59, 70, 81, 85}) {
			System.err.printf("(%d,%d) %d\n", i, 70,
					assignments[calc.eqVar(i, 70)] == Assign.TRUE ? 1 : 0);
		}*/

		NiceUnionFind unionFind = new NiceUnionFind(numStates);
		for (int i = 0; i < numStates; i++) {
			for (int j = i+1; j < numStates; j++) {
				int eqVar = calc.eqVar(i, j);
				if (assignments[eqVar] == Assign.TRUE) {
					//System.err.printf("merging X_%d,%d\n", i, j);
					unionFind.merge(i, j);
				}
			}
		}

		return NiceClasses.compress(unionFind.getRoots());
	}

	/**
	 * @param inNWA input NWA.
	 *
	 * @param history precalculated history states for <code>inNWA</code>.
	 *
	 * @return A (consistent) NiceClasses which represents the minimized
	 * automaton.
	 */
	public static ArrayList<HornClause3> generateConstraints(NiceNWA inNWA, ArrayList<NiceHist> history) {
		assert NiceHist.checkHistoryStatesConsistency(inNWA, history);
		{
		// "assert" that there are no transitions which are never taken
		HashSet<NiceHist> hs = new HashSet<NiceHist>();
		for (NiceHist h : history)
			hs.add(h);
		for (NiceRTrans x : inNWA.rTrans) {
			if (!hs.contains(new NiceHist(x.src, x.top)))
				System.err.printf("missing %d %d\n",  x.src, x.top);
			assert hs.contains(new NiceHist(x.src, x.top));
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
		NiceITrans[] iTrans = inNWA.iTrans.clone();
		NiceCTrans[] cTrans = inNWA.cTrans.clone();
		NiceRTrans[] rTrans = inNWA.rTrans.clone();

		history = new ArrayList<NiceHist>(history);

		// IMPORTANT. Sort inputs
		Arrays.sort(iTrans, NiceITrans::compareSrcSymDst);
		Arrays.sort(cTrans, NiceCTrans::compareSrcSymDst);
		Arrays.sort(rTrans, NiceRTrans::compareSrcTopSymDst);

		history.sort(NiceHist::compareLinHier);

		// All "outgoing" transitions, grouped by src, then sorted by (top), sym, dst
		ArrayList<ArrayList<NiceITrans>> iTransOut = new ArrayList<ArrayList<NiceITrans>>();
		ArrayList<ArrayList<NiceCTrans>> cTransOut = new ArrayList<ArrayList<NiceCTrans>>();
		ArrayList<ArrayList<NiceRTrans>> rTransOut = new ArrayList<ArrayList<NiceRTrans>>();

		for (int i = 0; i < numStates; i++) iTransOut.add(new ArrayList<NiceITrans>());
		for (int i = 0; i < numStates; i++) cTransOut.add(new ArrayList<NiceCTrans>());
		for (int i = 0; i < numStates; i++) rTransOut.add(new ArrayList<NiceRTrans>());

		for (int i = 0; i < numITrans; i++) iTransOut.get(iTrans[i].src).add(iTrans[i]);
		for (int i = 0; i < numCTrans; i++) cTransOut.get(cTrans[i].src).add(cTrans[i]);
		for (int i = 0; i < numRTrans; i++) rTransOut.get(rTrans[i].src).add(rTrans[i]);

		// OutSet is a combination of iSet, cSet, rSet and hSet as defined in the thesis
		OutSet[] outSet = new OutSet[numStates];
		for (int i = 0; i < numStates; i++) outSet[i] = new OutSet();

		for (int i = 0; i < numITrans; i++)	if (i == 0 || iTrans[i-1].src != iTrans[i].src || iTrans[i-1].sym != iTrans[i].sym) outSet[iTrans[i].src].iSet.add(iTrans[i].sym);
		for (int i = 0; i < numCTrans; i++)	if (i == 0 || cTrans[i-1].src != cTrans[i].src || cTrans[i-1].sym != cTrans[i].sym) outSet[cTrans[i].src].cSet.add(cTrans[i].sym);
		for (int i = 0; i < numRTrans; i++)	if (i == 0 || rTrans[i-1].src != rTrans[i].src || rTrans[i-1].top != rTrans[i].top) outSet[rTrans[i].src].rSet.add(rTrans[i].top);

		{
		// make the hSet, i.e. those history states except bottom-of-stack
		// symbol which are not in the outgoing return transitions as
		// top-of-stack symbol.
		int i = 0;
		for (NiceHist h : history) {
			for (; i < numRTrans; i++)
				if (h.lin < rTrans[i].src
						|| (h.lin == rTrans[i].src && h.hier <= rTrans[i].top))
					break;
			if (i == numRTrans
					|| h.lin < rTrans[i].src
					|| (h.lin == rTrans[i].src && h.hier < rTrans[i].top))
				if (h.hier >= 0) // could be bottom-of-stack (-1)
					outSet[h.lin].hSet.add(h.hier);
		}
		}
		/*
		System.err.printf("out sets:\n");
		for (int i = 0; i < numStates; i++) {
			System.err.printf("%d : %s\n", i, outSet[i].toString());
		}
		*/

		// group states by (iSet, cSet)
		HashMap<ICSet, ArrayList<Integer>> byICSet = new HashMap<ICSet, ArrayList<Integer>>();

		for (int i = 0; i < numStates; i++) {
			ICSet x = new ICSet(outSet[i].iSet, outSet[i].cSet);
			ArrayList<Integer> list = byICSet.get(x);
			if (list == null) {
				list = new ArrayList<Integer>();
				byICSet.put(x, list);
			}
			list.add(i);
		}
		System.err.printf("byICSet (%d states in %d groups):\n", numStates, byICSet.size());
		for (ArrayList<Integer> x : byICSet.values()) {
			System.err.printf(x.toString() + "\n");
		}
		System.err.printf("rSets and hSets:\n");
		for (int i = 0; i < numStates; i++) {
			System.err.printf("rset[%d] %s\nhset[%d] %s\n", i, outSet[i].rSet.toString(), i, outSet[i].hSet.toString());
		}


		/*
		 * GENERATE CLAUSES
		 *
		 */

		HornCNFBuilder builder = new HornCNFBuilder();
		EqVarCalc calc = new EqVarCalc(numStates);

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

		// separate states with differing out sets
		// NOTE: differing out sets means either their iSets or their cSets
		// are not equal. If they are equal, it could still be the case that
		// their rSets are not "compatible" but we handle that only later.
		{
			ArrayList<Integer> tmp = new ArrayList<Integer>();
			for (ArrayList<Integer> group : byICSet.values()) {
				for (int q1 : tmp) {
					for (int q2 : group) {
						//System.err.printf("outSet(%d) != outSet(%d), so adding clause: NOT X_%d,%d\n", q1, q2, q1, q2);
						int eq1 = calc.eqVar(q1, q2);
						builder.addClauseF(eq1);
					}
				}
				tmp.addAll(group);
			}
		}

		// clauses from rules 1, 2 and 3 for states with "equal" out sets
		// NOTE: equal out sets means that their iSets and cSets are equal.
		// We still need to check if their rSets are "compatible"
		for (ArrayList<Integer> group : byICSet.values()) {
			for (int i = 0; i < group.size(); i++) {
				for (int j = i+1; j < group.size(); j++) {
					int q1 = group.get(i);
					int q2 = group.get(j);
					assert q1 != q2;
					if (OutSet.outSetsIncompatible(outSet[q1], outSet[q2])) {
						int eq1 = calc.eqVar(q1, q2);
						//System.err.printf("outSet(%d) and outSet(%d) incompatible, so adding clause: NOT X_%d,%d\n", q1, q2, q1, q2);
						builder.addClauseF(eq1);
						// XXX: OBACHT!
						continue;
					}
					// rule 1
					for (NiceITrans x : iTransOut.get(q1)) {
						for (NiceITrans y : iTransOut.get(q2)) {
							if (x.sym == y.sym) {
								assert x.src == q1;
								assert y.src == q2;
								int eq1 = calc.eqVar(x.src, y.src);
								int eq2 = calc.eqVar(x.dst, y.dst);
								//System.err.printf("from rule 1: NOT X_%d,%d OR X_%d,%d\n", x.src, y.src, x.dst, y.dst);
								builder.addClauseFT(eq1, eq2);
							}
						}
					}
					// rule 2
					for (NiceCTrans x : cTransOut.get(q1)) {
						for (NiceCTrans y : cTransOut.get(q2)) {
							if (x.sym == y.sym) {
								assert x.src == q1;
								assert y.src == q2;
								int eq1 = calc.eqVar(x.src, y.src);
								int eq2 = calc.eqVar(x.dst, y.dst);
								//System.err.printf("from rule 2: NOT X_%d,%d OR X_%d,%d\n", x.src, y.src, x.dst, y.dst);
								builder.addClauseFT(eq1, eq2);
							}
						}
					}
					// rule 3
					for (NiceRTrans x : rTransOut.get(q1)) {
						for (NiceRTrans y : rTransOut.get(q2)) {
							if (x.sym == y.sym) {
								assert x.src == q1;
								assert y.src == q2;
								int eq1 = calc.eqVar(x.src, y.src);
								int eq2 = calc.eqVar(x.top, y.top);
								int eq3 = calc.eqVar(x.dst, y.dst);
								//System.err.printf("from rule 3: NOT X_%d,%d OR NOT X_%d,%d OR X_%d,%d\n", x.src, y.src, x.top, y.top, x.dst, y.dst);
								builder.addClauseFFT(eq1, eq2, eq3);
							}
						}
					}
				}
			}
		}

		// clauses for transitivity
		for (ArrayList<Integer> group : byICSet.values()) {
			for (int i = 0; i < group.size(); i++) {
				for (int j = i+1; j < group.size(); j++) {
					for (int k = j+1; k < group.size(); k++) {
						int eq1 = calc.eqVar(group.get(i), group.get(j));
						int eq2 = calc.eqVar(group.get(j), group.get(k));
						int eq3 = calc.eqVar(group.get(i), group.get(k));
						builder.addClauseFFT(eq1, eq2, eq3);
						builder.addClauseFFT(eq2, eq3, eq1);
						builder.addClauseFFT(eq3, eq1, eq2);
					}
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
		//System.err.printf("number of clauses: %d\n", clauses.size());
		//System.err.printf("number of clause-add requests: %d\n", builder.getNumRequests());

		return clauses;
	}
}

// combination of iSet, cSet, rSet and hSet as defined in the thesis:
// for a given state q,
//   iSet = i such that iTrans(q, i, *)
//   cSet = c such that cTrans(q, c, *)
//   rSet = q' such that rTrans(q, *, q', *)
//   hSet = q' such that history(q, q') AND NOT rTrans(q, *, q', *)
class OutSet {
	ArrayList<Integer> iSet;
	ArrayList<Integer> cSet;
	ArrayList<Integer> rSet;
	ArrayList<Integer> hSet;

	public OutSet() {
		iSet = new ArrayList<Integer>();
		cSet = new ArrayList<Integer>();
		rSet = new ArrayList<Integer>();
		hSet = new ArrayList<Integer>();
	}

	private static boolean nonemptyIntersection(ArrayList<Integer> a, ArrayList<Integer> b) {
		for (int i = 1; i < a.size(); i++) assert a.get(i) > a.get(i-1);
		for (int i = 1; i < b.size(); i++) assert b.get(i) > b.get(i-1);

		for (int i = 0, j = 0; i < a.size() && j < b.size();) {
			if (a.get(i) < b.get(j)) {
				i++;
			} else if (a.get(i) > b.get(j)) {
				j++;
			} else {
				return true;
			}
		}
		return false;
	}

	/**
	 * test for an indication of incompatible out sets (which means
	 * incompatible states).
	 */
	public static boolean outSetsIncompatible(OutSet a, OutSet b) {
		return (nonemptyIntersection(a.hSet, b.rSet) ||
				nonemptyIntersection(b.hSet, a.rSet));
	}

	@Override
	public String toString() {
		return "{" + iSet.toString() + " " + cSet.toString() + " " + rSet.toString() + " " + hSet.toString() + "}";
	}
}

class ICSet {
	ArrayList<Integer> iSet;
	ArrayList<Integer> cSet;

	public ICSet(ArrayList<Integer> iSet, ArrayList<Integer> cSet) {
		this.iSet = iSet;
		this.cSet = cSet;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj == null || !(obj instanceof ICSet)) return false;
		ICSet b = (ICSet) obj;
		return iSet.equals(b.iSet) && cSet.equals(b.cSet);
	}

	@Override
	public int hashCode() {
		return 31*iSet.hashCode() + cSet.hashCode();
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
