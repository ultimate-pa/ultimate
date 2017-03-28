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

import java.io.PrintWriter;
import java.io.StringWriter;
import java.io.Writer;
import java.util.ArrayList;

/**
 * A few static print methods.
 *
 * @author stimpflj
 */
final class Print {
	private Print() {
		// no public constructor
	}

	static void printPartition(final Writer writer, final Partition partition) {
		assert Partition.checkConsistency(partition);

		final ArrayList<ArrayList<Integer>> classes = new ArrayList<ArrayList<Integer>>();

		for (int i = 0; i < partition.mNumClasses; i++) {
			classes.add(new ArrayList<Integer>());
		}

		for (int i = 0; i < partition.mClassOf.length; i++) {
			classes.get(partition.mClassOf[i]).add(i);
		}

		final PrintWriter out = new PrintWriter(writer);

		for (final ArrayList<Integer> cls : classes) {
			out.print("{");
			for (final int i : cls) {
				out.printf(" %d", i);
			}
			out.print(" }");
		}

		out.print("%n");
		out.flush();
	}

	/**
	 * @param nwa
	 *            readonly NWA. Must have no null fields and must be constrained as suggested
	 */
	static void printNwa(final Writer writer, final NwaWithArrays nwa) {
		final ArrayList<Integer> initialStates = NwaWithArrays.computeInitialStates(nwa);
		final ArrayList<Integer> finalStates = NwaWithArrays.computeFinalStates(nwa);

		final PrintWriter p = new PrintWriter(writer);

		p.printf("numStates %d%n", nwa.mNumStates);
		p.printf("numISyms %d%n", nwa.mNumISyms);
		p.printf("numCSyms %d%n", nwa.mNumCSyms);
		p.printf("numRSyms %d%n", nwa.mNumRSyms);
		p.printf("numInitial %d%n", initialStates.size());
		p.printf("numFinal %d%n", finalStates.size());
		p.printf("numITrans %d%n", nwa.mITrans.length);
		p.printf("numCTrans %d%n", nwa.mCTrans.length);
		p.printf("numRTrans %d%n", nwa.mRTrans.length);

		for (final int i : initialStates) {
			p.printf("initial %d%n", i);
		}
		for (final int i : finalStates) {
			p.printf("final %d%n", i);
		}
		for (final ITrans x : nwa.mITrans) {
			p.printf("iTrans %d %d %d%n", x.mSrc, x.mSym, x.mDst);
		}
		for (final CTrans x : nwa.mCTrans) {
			p.printf("cTrans %d %d %d%n", x.mSrc, x.mSym, x.mDst);
		}
		for (final RTrans x : nwa.mRTrans) {
			p.printf("rTrans %d %d %d %d%n", x.mSrc, x.mSym, x.mTop, x.mDst);
		}

		p.flush();
	}

	static String makeString(final Partition cls) {
		final StringWriter w = new StringWriter();
		Print.printPartition(w, cls);
		return w.toString();
	}

	static String makeString(final NwaWithArrays nwa) {
		final StringWriter w = new StringWriter();
		Print.printNwa(w, nwa);
		return w.toString();
	}
}
