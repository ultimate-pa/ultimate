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
	public static final String s_RCFG_LABEL_ExternalSolver = "Use\\ external\\ solver\\ instead\\ of\\ SMTInterpol";
	public static final String s_RCFG_LABEL_BlockSize = "Size\\ of\\ a\\ code\\ block";
	public static final String s_RCFG_VALUE_Single = "SingleStatement";
	public static final String s_RCFG_VALUE_Seq = "SequenceOfStatements";
	public static final String s_RCFG_VALUE_Block = "LoopFreeBlock";
	public static final String s_RCFG_LABEL_RemoveGoto = "Remove\\ goto\\ edges\\ from\\ RCFG";
	public static final String s_RCFG_LABEL_Simplify = "Simplify\\ code\\ blocks";
	public static final String s_RCFG_LABEL_CNF = "Convert\\ code\\ blocks\\ to\\ CNF";
	
	public static final String s_TA_LABEL_Interpol = "Compute\\ Interpolants\\ along\\ a\\ Counterexample";
	public static final String s_TA_VALUE_CraigTree = "Craig_TreeInterpolation";
	
	public static final String s_BA_LABEL_ExtSolverRank = "Use\\ external\\ solver\\ (rank\\ synthesis)";
	public static final String s_BA_LABEL_Nonlinear = "Allow\\ nonlinear\\ constraints";
	
	public static final String s_LR_LABEL_only_nondecreasing_invariants = "Non-decreasing\\ invariants\\ only";
	public static final String s_LR_LABEL_nontermination_check_nonlinear = "Nonlinear\\ SMT\\ query\\ for\\ nontermination\\ check";
	public static final String s_LR_LABEL_termination_check_nonlinear = "Nonlinear\\ SMT\\ query\\ for\\ termination\\ check";
	public static final String s_LR_LABEL_use_external_solver = "Use\\ external\\ SMT\\ solver";
	
	public static final String s_LR_LABEL_nested_template_size = "Nested\\ template\\ size";
	public static final String s_LR_LABEL_multiphase_template_size = "Multiphase\\ template\\ size";
	public static final String s_LR_LABEL_lex_template_size = "Lexicographic\\ template\\ size";
	public static final String s_LR_LABEL_piecewise_template_size = "Piecewise\\ template\\ size";
	
	public static final String s_BE_LABEL_CALLMINIMIZE = "Minimize\\ Call\\ and\\ Return\\ Edges";
	public static final String s_BE_LABEL_STRATEGY = "Strategy\\ for\\ the\\ edge\\ rating";
	public static final String s_BE_VALUE_LargeBlock = "LARGE_BLOCK";
	public static final String s_BE_VALUE_DisjunctiveRating = "DISJUNCTIVE_RATING";
	public static final String s_BE_LABEL_RATINGBOUND = "Rating-Boundary\\ (empty\\ for\\ LBE)";
}
