package de.uni_freiburg.informatik.ultimate.website.toolchains;

/**
 * Class to store the Strings used by the web interface to build the correct
 * .epf files.
 * There Strings are exactly those which occur in the 
 * UltimatePreferenceInitializer file, but where the blank space is quoted with
 * backslash.
 * In the current architecture we do not want that the web interface depends
 * on all plugins therefore we have to copy all these strings. 
 * @author Matthias Heizmann
 *
 */
public class PrefStrings {
	public final static String s_RCFG_LABEL_ExternalSolver = "/Use\\ external\\ solver\\ instead\\ of\\ SMTInterpol";
	public final static String s_RCFG_LABEL_BlockSize = "/Size\\ of\\ a\\ code\\ block";
	public final static String s_RCFG_VALUE_Single = "SingleStatement";
	public final static String s_RCFG_VALUE_Seq = "SequenceOfStatements";
	public final static String s_RCFG_VALUE_Block = "LoopFreeBlock";
	public final static String s_TA_LABEL_Interpol = "/Compute\\ Interpolants\\ along\\ a\\ Counterexample";
	public final static String s_TA_VALUE_CraigTree = "Craig_TreeInterpolation";
	public final static String s_BA_LABEL_ExtSolverRank = "Command\\ for\\ external\\ solver\\ (rank\\ synthesis)";

}
