package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

public class HeapSepSettings {


	private final boolean mDumpPrograms = true;

	private final String mDumpProgramsPath = "C:\\Temp\\automata";

	private final boolean mCrashOnArrayAssume = true;

	/**
	 *
	 * not clear:
	 *  <li> how much of a slowdown this causes
	 *  <li> if it is only necessary for assertions or not
	 */
	private final boolean mAssumeFreezeVarLitDisequalitiesAtInitEdges = false;

	private final boolean mAssertFreezeVarLitDisequalitiesIntoScript = true;

	private final boolean mAddLiteralDisequalitiesAsAxioms = false;

	public boolean isAssumeFreezeVarLitDisequalitiesAtInitEdges() {
		return mAssumeFreezeVarLitDisequalitiesAtInitEdges;
	}

	public boolean isAddLiteralDisequalitiesAsAxioms() {
		return mAddLiteralDisequalitiesAsAxioms;
	}

	public boolean isAssertFreezeVarLitDisequalitiesIntoScript() {
		return mAssertFreezeVarLitDisequalitiesIntoScript;
	}

	/**
	 * Dump the programs (input program, program as fed to equality domain, transformed program) to disk as automata
	 * (via {@link CFG2Automaton}.
	 *
	 * @return
	 */
	public boolean isDumpPrograms() {
		return mDumpPrograms;
	}

	/**
	 * Path used if {@link #isDumpPrograms()} is set.
	 *
	 * @return
	 */
	public String getDumpProgramsPath() {
		return mDumpProgramsPath;
	}

	/**
	 * Our technique does not handle assumes between arrays, if those arrays are supposed to be separated.
	 * (Not yet used, not clear what else to do but crash..)
	 *
	 * @return
	 */
	public boolean isCrashOnArrayAssume() {
		return mCrashOnArrayAssume;
	}
}