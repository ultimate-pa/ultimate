package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences;

public class PreferenceValues {

	/*
	 * Names for the preferences
	 */
	public static String NAME_INTERPROCEDUTAL = "Interprocedural";
	public static String NAME_LETTER = "BlockSize";
	public static String NAME_TIMEOUT = "Timeout";
	public static String NAME_ITERATIONS = "Iterations";
	public static String NAME_ARTIFACT = "Artifact";
	public static String NAME_WATCHITERATION = "ObservedIteration";
	public static String NAME_HOARE = "HoareAnnotation";
	public static String NAME_INTERPOLATED_LOCS = "Interpolants";
	public static String NAME_InterpolantAutomaton = "InterpolantAutomaton";
	public static String NAME_EDGES2TRUE = "Edges2True";
	public static String NAME_DUMPSCRIPT = "DumpScript";
	public static String NAME_DUMPFORMULAS = "DumpFormulas";
	public static String NAME_DUMPAUTOMATA = "DumpAutomata";
	public static String NAME_DUMPPATH = "DumpPath";
	public static String NAME_SOLVER = "Solver";
	
	public static String NAME_DETERMINIZATION = "Determinization";
	public static String NAME_DIFFERENCE_SENWA = "DifferenceSenwa";
	public static String NAME_MINIMIZE = "Minimize";
	public static String NAME_CONCURRENCY = "Concurrency";
	public static String NAME_AllErrorsAtOnce = "AllErrorsAtOnce";
	public static final String NAME_Order = "Order";
	public static final String NAME_cutOff = "cutOff";
	public static final String NAME_unfolding2Net = "unfolding2Net";
	public static final String NAME_simplifyCodeBlocks = "simplifyCodeBlocks";
	public static final String NAME_PreserveGotoEdges = "PreserveGotoEdges";
	
	/*
	 * labels for the different preferencess
	 */
	public static String LABEL_INTERPROCEDUTAL =
		"Interprocedural analysis (Nested Interpolants)";
	public static String LABEL_AllErrorsAtOnce =
		"Check all specifiacations at once";
	public static String LABEL_LETTER =
		"What is a letter in the trace abstraction alpabet";
	public static String LABEL_SOLVER =
		"Interpolating solver";
	public static String LABEL_TIMEOUT =
		"Timeout in seconds";
	public static String LABEL_ITERATIONS =
		"Iterations until the model checker surrenders";
	public static String LABEL_ARTIFACT	=
		"Kind of artifact that is visualized";
	public static String LABEL_OBSERVEDITERATION = 
		"Number of iteration whose artifact is visualized";
	public static String LABEL_HOARE = 
		"Compute Hoare Annotation of negated interpolant automaton, abstraction and CFG";
	public static String LABEL_INTERPOLATED_LOCS	=
		"Compute Interpolants along a Counterexample";
	public static String LABEL_EDGES2TRUE = 
		"Add backedges from every state to initial state";
	public static String LABEL_InterpolantAutomaton	=
		"Interpolant automaton";
	public static String LABEL_DUMPSCRIPT =
		"Dump SMT script to file";
	public static String LABEL_DUMPFORMULAS =
		"Dump interpolation problems and satisfiability problems to files";
	public static String LABEL_DUMPAUTOMATA =
		"Dump automata to files";
	public static String LABEL_DUMPPATH =
		"Dump formulas of problems in the following path";
	public static final String LABEL_DETERMINIZATION =
		"Determinization algorithm";
	public static final String LABEL_DIFFERENCE_SENWA =
		"DifferenceSenwa operation instead classical Difference";
	public static final String LABEL_MINIMIZE =
		"Minimize abstraction";
	public static final String LABEL_CONCURRENCY =
		"Automaton type used in concurrency analysis";
	public static final String LABEL_Order = 
			"Order in Petri net unfolding";
	public static final String LABEL_cutOff = 
			"cut-off requires same transition";
	public static final String LABEL_unfolding2Net = 
			"use unfolding as abstraction";
	public static final String LABEL_simplifyCodeBlocks = 
			"simplify CodeBlocks";
	public static final String LABEL_PreserveGotoEdges =
			"Preserve Goto-Edges in RCFG";

	public enum INTERPOLATION { Craig_NestedInterpolation, Craig_TreeInterpolation, ForwardPredicates, BackwardPredicates, FPandSP };
	
	public static final String VALUE_LETTER_STATEMENT = "single program statement";
	public static final String VALUE_LETTER_SEQUENCE = "sequence of program statements";
	public static final String VALUE_LETTER_BLOCK = "loop free block";
	public static final Solver VALUE_SOLVER_SMTINTERPOL = Solver.SMTInterpol;
	public static final Solver VALUE_SOLVER_Z3 = Solver.Z3;
	public static final String VALUE_ABSTRACTION = "Abstraction";
	public static final String VALUE_RCFG = "RecursiveControlFlowGraph";
	public static final String VALUE_INTERPOLANT_AUTOMATON = "InterpolantAutomaton";
	public static final String VALUE_NEG_INTERPOLANT_AUTOMATON = "NegatedInterpolantAutomaton";
//	public static final String VALUE_ALL_LOC = "Craig - all locations";
//	public static final String VALUE_CUTPOINTS = "Craig - Cutpoints";
	public static final String VALUE_ITP_WP = "StrongestPostcondition&WeakestPrecondition";
	public static final String VALUE_ITP_GUESS = "Guess Interpolants";
	public static final String VALUE_InterpolantAutomaton_SingleTrace = "SingleTrace";
	public static final String VALUE_InterpolantAutomaton_TwoTrack = "TwoTrack";
	public static final String VALUE_InterpolantAutomaton_Canonical = "With backedges to repeated locations (Canonial)";
	public static final String VALUE_InterpolantAutomaton_TotalInterpolation = "Total interpolation (Jan)";
	
	//Values of Determinization
	public static final String VALUE_POWERSET= "Powerset";
	public static final String VALUE_BESTAPPROXIMATION = "Best Approximation";
	public static final String VALUE_SELFLOOP = "Add as many selfloops as possible";
	public static final String VALUE_STRONGESTPOST = "Strongest Post";
	public static final String VALUE_EAGERPOST = "EagerPost";
	public static final String VALUE_LAZYPOST = "LazyPost";
	
	public static final String VALUE_FINITE_AUTOMATON = "Finite Automata";
	public static final String VALUE_PETRI_NET = "Petri Net";
	public static final String VALUE_KMM = "Ken McMillan";
	public static final String VALUE_EVR = "Esparza Römer Vogler";
	public static final String VALUE_EVRMark = "ERV with equal markings";


	
	/*
	 * default values for the different preferences
	 */
	public static final boolean DEF_INTERPROCEDUTAL = true;
	public static final String DEF_LETTER = VALUE_LETTER_BLOCK;
	public static final Solver DEF_SOLVER = Solver.SMTInterpol;
	public static final int DEF_ITERATIONS = 10000;
	public static final int DEF_TIMEOUT = 1000;
	public static final String DEF_ARTIFACT	= VALUE_RCFG;
	public static final int DEF_WATCHITERATION = 1000;
	public static final boolean DEF_HOARE = false;
	public static final INTERPOLATION DEF_INTERPOLANTS = INTERPOLATION.Craig_NestedInterpolation;
	public static final boolean DEF_EDGES2TRUE = false;
	public static final String DEF_ADDITIONAL_EDGES = VALUE_InterpolantAutomaton_Canonical;
	public static final boolean DEF_DUMPSCRIPT = false;
	public static final boolean DEF_DUMPFORMULAS = false;
	public static final boolean DEF_DUMPAUTOMATA = false;
	public static final String DEF_DUMPPATH = ".";
	public static final String DEF_DETERMINIZATION = VALUE_STRONGESTPOST;
	public static final boolean DEF_DIFFERENCE_SENWA = false;
	public static final boolean DEF_MINIMIZE = true;
	public static final String DEF_CONCURRENCY = VALUE_PETRI_NET;
	public static final boolean DEF_AllErrorsAtOnce = true;


	public static final boolean DEF_cutOff = true;
	public static final boolean DEF_unfolding2Net = false;
	public static final String DEF_Order = VALUE_EVR;
	public static final boolean DEF_simplifyCodeBlocks = false;
	public static final boolean DEF_PreserveGotoEdges = false;

	
	public enum Solver { Z3, SMTInterpol }
	
}
