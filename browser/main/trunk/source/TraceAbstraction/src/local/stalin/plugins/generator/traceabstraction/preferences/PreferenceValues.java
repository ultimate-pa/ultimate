/**
 * 
 */
package local.stalin.plugins.generator.traceabstraction.preferences;


public class PreferenceValues {

	/*
	 * Names for the different preferences
	 */
	public static String NAME_INTERPROCEDUTAL = "Interprocedural";
	public static String NAME_ITERATIONS = "Iterations";
	public static String NAME_ARTIFACT = "Artifact";
	public static String NAME_WATCHITERATION = "ObservedIteration";
	public static String NAME_INTERPOLATED_LOCS = "Interpolants";
	public static String NAME_ADDITIONAL_EDGES = "AdditionalEdges";
	public static String NAME_EDGES2TRUE = "Edges2True";
	public static String NAME_DUMPFORMULAS = "DumpFormulas";
	public static String NAME_DUMPAUTOMATA = "DumpAutomata";
	public static String NAME_DUMPPATH = "DumpPath";
	public static String NAME_SOLVER = "Solver";
	
	public static String NAME_DETERMINIZATION = "Determinization";
	public static String NAME_DIFFERENCE = "Difference";
	public static String NAME_MINIMIZE = "Minimize";
	
	/*
	 * labels for the different preferencess
	 */
	public static String LABEL_INTERPROCEDUTAL =
		"Interprocedural analysis (Nested Interpolants)";
	public static String LABEL_SOLVER =
		"Interpolating solver";
	public static String LABEL_ITERATIONS =
		"Iterations until the model checker surrenders";
	public static String LABEL_ARTIFACT	=
		"Kind of artifact that is visualized";
	public static String LABEL_OBSERVEDITERATION = 
		"Number of iteration whose artifact is visualized";
	public static String LABEL_INTERPOLATED_LOCS	=
		"Compute Interpolants along a Counterexample";
	public static String LABEL_EDGES2TRUE = 
		"Add backedges from every state to initial state";
	public static String LABEL_ADDITIONAL_EDGES	=
		"Add Additional Edges";
	public static String LABEL_DUMPFORMULAS =
		"Dump interpolation problems and satisfiability problems to files";
	public static String LABEL_DUMPAUTOMATA =
		"Dump automata to files";
	public static String LABEL_DUMPPATH =
		"Dump formulas of problems in the following path";
	public static final String LABEL_DETERMINIZATION =
		"Determinization algorithm";
	public static final String LABEL_DIFFERENCE =
		"Difference operation instead of complement and intersection";
	public static final String LABEL_MINIMIZE =
		"Minimize abstraction";
	
	
	public static final String VALUE_SOLVER_SMTINTERPOL = "SMTINTERPOL";
	public static final String VALUE_SOLVER_GROUNDIFY = "GROUNDIFY";
	public static final String VALUE_ABSTRACTION = "Abstraction";
	public static final String VALUE_RCFG = "RecursiveControlFlowGraph";
	public static final String VALUE_INTERPOLANT_AUTOMATON = "InterpolantAutomaton";
	public static final String VALUE_NEG_INTERPOLANT_AUTOMATON = "NegatedInterpolantAutomaton";
	public static final String VALUE_ALL_LOC = "All locations";
	public static final String VALUE_CUTPOINTS = "Cutpoints";
	public static final String VALUE_NO_EDGE = "None";
	public static final String VALUE_CANONICAL = "Backedges to repeated locations (Canonial)";
	public static final String VALUE_EAGER = "All edges (Eager)";
	
	//Values of Determinization
	public static final String VALUE_POWERSET= "Powerset";
	public static final String VALUE_BESTAPPROXIMATION = "Best Approximation";
	public static final String VALUE_SELFLOOP = "Add as many selfloops as possible";



	
	/*
	 * default values for the different preferences
	 */
	public static final boolean DEF_INTERPROCEDUTAL = false;
	public static final String DEF_SOLVER = VALUE_SOLVER_SMTINTERPOL;
	public static final int DEF_ITERATIONS = 1000;
	public static final String DEF_ARTIFACT	= VALUE_INTERPOLANT_AUTOMATON;
	public static final int DEF_WATCHITERATION = 1000;
	public static final String DEF_INTERPOLANTS = VALUE_CUTPOINTS;
	public static final boolean DEF_EDGES2TRUE = false;
	public static final String DEF_ADDITIONAL_EDGES = VALUE_CANONICAL;
	public static final boolean DEF_DUMPFORMULAS = false;
	public static final boolean DEF_DUMPAUTOMATA = false;
	public static final String DEF_DUMPPATH = ".";
	public static final String DEF_DETERMINIZATION = VALUE_POWERSET;
	public static final boolean DEF_DIFFERENCE = true;
	public static final boolean DEF_MINIMIZE = true;
	
}
