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

import java.io.Writer;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;

/**
 * A few static print methods
 *
 * @author stimpflj
 *
 */
final class Print {

	static void printPartition(Writer writer, Partition partition) {
		assert Partition.checkConsistency(partition);

		ArrayList<ArrayList<Integer>> classes = new ArrayList<ArrayList<Integer>>();

		for (int i = 0; i < partition.numClasses; i++)
			classes.add(new ArrayList<Integer>());

		for (int i = 0; i < partition.classOf.length; i++)
			classes.get(partition.classOf[i]).add(i);

		PrintWriter out = new PrintWriter(writer);

		for (ArrayList<Integer> cls : classes) {
			out.print("{");
			for (int i : cls)
				out.printf(" %d", i);
			out.print(" }");
		}

		out.print("\n");
		out.flush();
	}

	/**
	 * @param nwa
	 *            readonly NWA. Must have no null fields and must be constrained
	 *            as suggested
	 * @param out
	 */
	static void printNWA(Writer writer, NWA nwa) {
		ArrayList<Integer> initialStates = NWA.computeInitialStates(nwa);
		ArrayList<Integer> finalStates = NWA.computeFinalStates(nwa);

		PrintWriter p = new PrintWriter(writer);

		p.printf("numStates %d\n", nwa.numStates);
		p.printf("numISyms %d\n",  nwa.numISyms);
		p.printf("numCSyms %d\n",  nwa.numCSyms);
		p.printf("numRSyms %d\n",  nwa.numRSyms);
		p.printf("numInitial %d\n", initialStates.size());
		p.printf("numFinal %d\n",  finalStates.size());
		p.printf("numITrans %d\n", nwa.iTrans.length);
		p.printf("numCTrans %d\n", nwa.cTrans.length);
		p.printf("numRTrans %d\n", nwa.rTrans.length);

		for (int i : initialStates)
			p.printf("initial %d\n", i);
		for (int i : finalStates)
			p.printf("final %d\n", i);
		for (ITrans x : nwa.iTrans)
			p.printf("iTrans %d %d %d\n", x.src, x.sym, x.dst);
		for (CTrans x : nwa.cTrans)
			p.printf("cTrans %d %d %d\n", x.src, x.sym, x.dst);
		for (RTrans x : nwa.rTrans)
			p.printf("rTrans %d %d %d %d\n", x.src, x.sym, x.top, x.dst);

		p.flush();
	}

	static String makeString(Partition cls) {
		StringWriter w = new StringWriter();
		Print.printPartition(w,  cls);
		return w.toString();
	}

	static String makeString(NWA nwa) {
		StringWriter w = new StringWriter();
		Print.printNWA(w,  nwa);
		return w.toString();
	}
}
