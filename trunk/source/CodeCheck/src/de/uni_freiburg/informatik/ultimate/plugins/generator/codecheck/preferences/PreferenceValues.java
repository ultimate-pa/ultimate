package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceValues.INTERPOLATION;

public class PreferenceValues {
	
	public enum SolverAndInterpolator { SMTINTERPOL, Z3SPWP }
	public enum EdgeCheckOptimization { NONE, PUSHPOP, SDEC, PUSHPOP_SDEC }
	public enum PredicateUnification { PER_ITERATION, PER_VERIFICATION, NONE } 
	public enum Solver { Z3, SMTInterpol }
	
	/*
	 * Names for the preferences
	 */
	public static String NAME_ONLYMAINPROCEDURE = "onlyMainProcedure"; 
	public static String NAME_MEMOIZENORMALEDGECHECKS = "memoizeNormalEdgeChecks";
	public static String NAME_MEMOIZERETURNEDGECHECKS = "memoizeReturnEdgeChecks";

	public static String NAME_SOLVERANDINTERPOLATOR = "SolverAndInterpolator";
	public static String NAME_INTERPOLATIONMODE = "InterpolationMode";
	public static String NAME_PREDICATEUNIFICATION = "PredicateUnificationMode";
	public static String NAME_EDGECHECKOPTIMIZATION = "EdgeCheckOptimizationMode";
	
	public static String NAME_GRAPHWRITERPATH = "DestinationForGotGraphs";
	
	public static String NAME_TIMEOUT = "TimeoutInSeconds";
	
	/*
	 * labels for the different preferencess
	 */
	public static String LABEL_ONLYMAINPROCEDURE =
		"only verify starting from main procedure";
	public static String LABEL_MEMOIZENORMALEDGECHECKS =
		"memoize already made edge checks for non-return edges";
	public static String LABEL_MEMOIZERETURNEDGECHECKS =
		"memoize already made edge checks for return edges";

	public static String LABEL_SOLVERANDINTERPOLATOR =
		"Interpolating solver";	
	public static String LABEL_INTERPOLATIONMODE =
		"tree interpolation mode for smtinterpol \n (internal: tree, a la matthias: nested)";	
	public static String LABEL_PREDICATEUNIFICATION =
		"Predicate Unification Mode";
	public static String LABEL_EDGECHECKOPTIMIZATION =
		"EdgeCheck Optimization Mode";
	
	public static String LABEL_GRAPHWRITERPATH =
		"write dot graph files here (empty for don't write)";

	public static String LABEL_TIMEOUT =
			"Timeout in seconds";

	public static final SolverAndInterpolator VALUE_SOLVERANDINTERPOLATOR_SMTINTERPOL = SolverAndInterpolator.SMTINTERPOL;
	public static final SolverAndInterpolator VALUE_SOLVERANDINTERPOLATOR_Z3SPWP = SolverAndInterpolator.Z3SPWP;
	
	public static final INTERPOLATION VALUE_INTERPOLATIONMODE_TREE = INTERPOLATION.Craig_TreeInterpolation;
	public static final INTERPOLATION VALUE_INTERPOLATIONMODE_NESTED = INTERPOLATION.Craig_NestedInterpolation;
	
	public static final PredicateUnification VALUE_PREDICATEUNIFICATION_PERVERIFICATION = PredicateUnification.PER_VERIFICATION;
	public static final PredicateUnification VALUE_PREDICATEUNIFICATION_PERITERATION = PredicateUnification.PER_ITERATION;
	public static final PredicateUnification VALUE_PREDICATEUNIFICATION_NONE = PredicateUnification.NONE;
	
	public static final EdgeCheckOptimization VALUE_EDGECHECKOPTIMIZATION_NONE = EdgeCheckOptimization.NONE;
	public static final EdgeCheckOptimization VALUE_EDGECHECKOPTIMIZATION_SDEC = EdgeCheckOptimization.SDEC;
	public static final EdgeCheckOptimization VALUE_EDGECHECKOPTIMIZATION_PUSHPOP = EdgeCheckOptimization.PUSHPOP;
	public static final EdgeCheckOptimization VALUE_EDGECHECKOPTIMIZATION_PUSHPOPSDEC = EdgeCheckOptimization.PUSHPOP_SDEC;
	
//	/*
//	 * default values for the different preferences
//	 */
	public static final boolean DEF_ONLYMAINPROCEDURE = false;
	public static final boolean DEF_MEMOIZENORMALEDGECHECKS = true;
	public static final boolean DEF_MEMOIZERETURNEDGECHECKS = true;
	
	public static final SolverAndInterpolator DEF_SOLVERANDINTERPOLATOR = SolverAndInterpolator.SMTINTERPOL;
	public static final INTERPOLATION DEF_INTERPOLATIONMODE = INTERPOLATION.Craig_TreeInterpolation;
//	public static final PredicateUnification DEF_PREDICATEUNIFICATION = PredicateUnification.PER_VERIFICATION;
	public static final PredicateUnification DEF_PREDICATEUNIFICATION = PredicateUnification.PER_ITERATION;
	public static final EdgeCheckOptimization DEF_EDGECHECKOPTIMIZATION = EdgeCheckOptimization.NONE;
	
	public static final String DEF_GRAPHWRITERPATH = "";
	
	public static final int DEF_TIMEOUT = 1000;
}
