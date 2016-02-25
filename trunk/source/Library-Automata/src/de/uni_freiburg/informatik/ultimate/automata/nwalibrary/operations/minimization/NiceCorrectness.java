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

import java.io.BufferedWriter;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

/**
 * @author stimpflj
 *
 */
public class NiceCorrectness {

	/**
	 * NOTE: This code started as copy&paste from
	 * NwaMinimizationClausesGenerator. Unless there is a better way to
	 * test correctness, just don't modify this class.
	 */
	static void testCorrectness(NiceNWA inNWA, ArrayList<NiceHist> history, NiceClasses niceClasses) {
		NicePrint.printClasses(new BufferedWriter(new PrintWriter(System.err)), niceClasses);

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
		NiceITrans[] iTrans = inNWA.iTrans;
		NiceCTrans[] cTrans = inNWA.cTrans;
		NiceRTrans[] rTrans = inNWA.rTrans;

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
		// we do it using a hashmap of ICSet here
		ICSet[] icSet = new ICSet[numStates];
		for (int i = 0; i < numStates; i++) icSet[i] = new ICSet(outSet[i].iSet, outSet[i].cSet);

		HashMap<ICSet, ArrayList<Integer>> byICSet = new HashMap<ICSet, ArrayList<Integer>>();

		for (int i = 0; i < numStates; i++) {
			ICSet x = icSet[i];
			ArrayList<Integer> list = byICSet.get(x);
			if (list == null) {
				list = new ArrayList<Integer>();
				byICSet.put(x, list);
			}
			list.add(i);
		}
		/*
		System.err.printf("byICSet:\n");
		for (ArrayList<Integer> x : byICSet.values()) {
			System.err.printf(x.toString() + "\n");
		}
		*/

		int numClasses = niceClasses.numClasses;
		int classOf[] = niceClasses.classOf;

		ArrayList<ArrayList<Integer>> classes = new ArrayList<ArrayList<Integer>>();
		for (int i = 0; i < numClasses; i++) classes.add(new ArrayList<Integer>());
		for (int i = 0; i < numStates; i++) classes.get(classOf[i]).add(i);
		for (int i = 0; i < numClasses; i++) assert classes.get(i).size() > 0;

		for (ArrayList<Integer> cls : classes) {
			for (int i = 1; i < cls.size(); i++) {
				int q1 = cls.get(i-1);
				int q2 = cls.get(i);
				// rule 0
				assert isFinal[q1] == isFinal[q2];
				// rules 1 and 2, partly
				assert icSet[q1].equals(icSet[q2]);
				// rule 3, partly
				/*System.err.printf("outSet[%d].rSet: %s\n", q1, outSet[q1].rSet.toString());
				System.err.printf("outSet[%d].hSet: %s\n", q1, outSet[q1].hSet.toString());
				System.err.printf("outSet[%d].rSet: %s\n", q2, outSet[q2].rSet.toString());
				System.err.printf("outSet[%d].hSet: %s\n", q2, outSet[q2].hSet.toString());
				*/
				assert !OutSet.outSetsIncompatible(outSet[q1], outSet[q2]);
			}
			for (int i = 0; i < cls.size(); i++) {
				for (int j = i+1; j < cls.size(); j++) {
					int q1 = cls.get(i);
					int q2 = cls.get(j);
					assert q1 != q2;
					if (OutSet.outSetsIncompatible(outSet[q1], outSet[q2])) {
						// XXX: OBACHT!
						continue;
					}
					// rule 1, rest
					for (NiceITrans x : iTransOut.get(q1)) {
						for (NiceITrans y : iTransOut.get(q2)) {
							if (x.sym == y.sym) {
								assert x.src == q1;
								assert y.src == q2;
								assert classOf[x.dst] == classOf[y.dst];
							}
						}
					}
					// rule 2, rest
					for (NiceCTrans x : cTransOut.get(q1)) {
						for (NiceCTrans y : cTransOut.get(q2)) {
							if (x.sym == y.sym) {
								assert x.src == q1;
								assert y.src == q2;
								assert classOf[x.dst] == classOf[y.dst];
							}
						}
					}
					// rule 3
					for (NiceRTrans x : rTransOut.get(q1)) {
						for (NiceRTrans y : rTransOut.get(q2)) {
							if (x.sym == y.sym) {
								assert x.src == q1;
								assert y.src == q2;
								assert classOf[x.top] != classOf[y.top]
									|| classOf[x.dst] == classOf[y.dst];
							}
						}
					}
				}
			}
		}
	}
}