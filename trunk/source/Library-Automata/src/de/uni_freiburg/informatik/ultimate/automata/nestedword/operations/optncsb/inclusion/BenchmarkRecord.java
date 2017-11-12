/*
 * Copyright (C) 2017 Yong Li (liyong@ios.ac.cn)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.text.SimpleDateFormat;
import java.util.Date;

/**
 * This class is used to record the information of generated interpolant automaton at each iteration
 */
public class BenchmarkRecord {

	private static int mNumOfNBAs = 0;
	private static int mNumOfSDBAs = 0;
	private static int mNumOfDBAs = 0;
	private static int mNumOfFAs = 0;
	// private static List<AutomatonInfo> mInfoOfInterpolantAtIteration;
	// private static List<AutomatonInfo> mInfoOfCeAtIteration;
	private static PrintWriter mOutput = null;
	private static String mOutputFile = null;

	public static boolean includeDiffTransition() {
		return true;
	}
	
	public static boolean canDump() {
		File f = new File("machine.conf");
		if(f.exists()) { 
			return true;
		}
		return false;
	}

	private BenchmarkRecord() {

	}

	private static enum AutomatonType {
		NBA, SDBA, DBA, FA;

		@Override
		public String toString() {
			if (this == NBA) {
				return "NBA";
			} else if (this == SDBA) {
				return "SDBA";
			} else if (this == DBA) {
				return "DBA";
			} else {
				return "FA";
			}
		}
	}

	private static class AutomatonInfo {
		int mNumOfStates;
		int mNumOfTrans;
		AutomatonType mAutType;
		int mIteration;

		AutomatonInfo(final int iteration, final int numOfStates, final int numOfTrans, final AutomatonType autType) {
			mIteration = iteration;
			mNumOfStates = numOfStates;
			mNumOfTrans = numOfTrans;
			mAutType = autType;
		}

		@Override
		public String toString() {
			return "( " + mIteration + ", " + mNumOfStates + ", " + mNumOfTrans + ", " + mAutType + ")";
		}
	}

	public static void start(final String name, final String algorithm) {
		if (mOutputFile == null) {
			mOutputFile = "Info.log";
		}
		try {
			mOutput = new PrintWriter(new BufferedWriter(new FileWriter(mOutputFile, true)));
		} catch (final IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		mOutput.println("\n" + name);
		mOutput.println(algorithm);
		mOutput.close();
		clear();
	}

	private static void clear() {
		mNumOfNBAs = 0;
		mNumOfSDBAs = 0;
		mNumOfDBAs = 0;
		mNumOfFAs = 0;
		// mInfoOfInterpolantAtIteration = new ArrayList<>();
		// mInfoOfCeAtIteration = new ArrayList<>();
	}

	public static void addComplementAutomaton(final int iteration, final int numOfStates, final int numOfTrans) {
		if (mOutputFile == null) {
			return;
		}
		try {
			mOutput = new PrintWriter(new BufferedWriter(new FileWriter(mOutputFile, true)));
			mOutput.print("(" + iteration + ", " + numOfStates + "), ");
			mOutput.close();
		} catch (final IOException e) {
			e.printStackTrace();
		}
	}
	
	public static void addDiffComparison(final int numOfStatesOfBA, final int numOfStatesOfGBA, final int numOfStatesOfGBA2BA) {
		if (mOutputFile == null) {
			return;
		}
		try {
			mOutput = new PrintWriter(new BufferedWriter(new FileWriter(mOutputFile, true)));
			mOutput.print("( BA:" + numOfStatesOfBA + ", GBA: " + numOfStatesOfGBA + ", GBA2BA: " + numOfStatesOfGBA2BA + "), ");
			mOutput.close();
		} catch (final IOException e) {
			e.printStackTrace();
		}
	}

	public static void addInterpolantOrDifferenceAutomaton(final int iteration, final int numOfStates,
			final int numOfTrans, final int type, final int numOfStatesOfDiff, final int numOfTransOfDiff) {

		AutomatonType autType = null;
		if (type == 0) {
			autType = AutomatonType.NBA;
			mNumOfNBAs++;
		} else if (type == 1) {
			autType = AutomatonType.SDBA;
			mNumOfSDBAs++;
		} else if (type == 2) {
			autType = AutomatonType.DBA;
			mNumOfDBAs++;
		} else if (type == 3) {
			autType = AutomatonType.FA;
			mNumOfFAs++;
		}
		if (mOutputFile == null) {
			return;
		}
		try {
			mOutput = new PrintWriter(new BufferedWriter(new FileWriter(mOutputFile, true)));
		} catch (final IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		final AutomatonInfo info = new AutomatonInfo(iteration, numOfStates, numOfTrans, autType);
		mOutput.print("[" + info + ", " + numOfStatesOfDiff + ", " + numOfTransOfDiff + "], ");
		mOutput.close();
	}

	public static void finish() {
		if (mOutputFile == null) {
			return;
		}
		try {
			mOutput = new PrintWriter(new BufferedWriter(new FileWriter(mOutputFile, true)));
		} catch (final IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		mOutput.println();
		mOutput.println("# interpolant NBAs = " + mNumOfNBAs);
		mOutput.println("# interpolant SDBAs = " + mNumOfSDBAs);
		mOutput.println("# interpolant DBAs = " + mNumOfDBAs);
		mOutput.println("# interpolant FAs = " + mNumOfFAs);
		mOutput.close();
	}
}
