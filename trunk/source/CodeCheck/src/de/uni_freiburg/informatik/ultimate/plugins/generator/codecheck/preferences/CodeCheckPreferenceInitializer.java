package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences;

import java.util.prefs.PreferenceChangeEvent;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;

public class CodeCheckPreferenceInitializer extends UltimatePreferenceInitializer {

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
//				new UltimatePreferenceItem<Boolean>(LABEL_ONLYMAINPROCEDURE,
//						DEF_ONLYMAINPROCEDURE, PreferenceType.Boolean),
				new UltimatePreferenceItem<Checker>(
						LABEL_CHECKER, DEF_CHECKER, 
						PreferenceType.Combo, Checker.values()),
				new UltimatePreferenceItem<Boolean>(
						LABEL_MEMOIZENORMALEDGECHECKS,
						DEF_MEMOIZENORMALEDGECHECKS, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_MEMOIZERETURNEDGECHECKS,
						DEF_MEMOIZERETURNEDGECHECKS, PreferenceType.Boolean),
				new UltimatePreferenceItem<SolverAndInterpolator>(
						LABEL_SOLVERANDINTERPOLATOR, DEF_SOLVERANDINTERPOLATOR,
						PreferenceType.Combo, SolverAndInterpolator.values()),
				new UltimatePreferenceItem<INTERPOLATION>(
						LABEL_INTERPOLATIONMODE, DEF_INTERPOLATIONMODE,
						PreferenceType.Combo, INTERPOLATION.values()),
				new UltimatePreferenceItem<PredicateUnification>(
						LABEL_PREDICATEUNIFICATION, DEF_PREDICATEUNIFICATION,
						PreferenceType.Combo, PredicateUnification.values()),
				new UltimatePreferenceItem<EdgeCheckOptimization>(
						LABEL_EDGECHECKOPTIMIZATION, DEF_EDGECHECKOPTIMIZATION,
						PreferenceType.Combo, EdgeCheckOptimization.values()),
				new UltimatePreferenceItem<String>(LABEL_GRAPHWRITERPATH,
						DEF_GRAPHWRITERPATH, PreferenceType.Directory),
				new UltimatePreferenceItem<Integer>(LABEL_TIMEOUT, DEF_TIMEOUT,
						PreferenceType.Integer,
						new IUltimatePreferenceItemValidator.IntegerValidator(
								0, 1000000)),
				new UltimatePreferenceItem<Integer>(LABEL_ITERATIONS, DEF_ITERATIONS,
						PreferenceType.Integer, new IUltimatePreferenceItemValidator.IntegerValidator(
								-1, 1000000)),
				new UltimatePreferenceItem<RedirectionStrategy>(LABEL_REDIRECTION, DEF_REDIRECTION,
						PreferenceType.Combo, RedirectionStrategy.values()),

				new UltimatePreferenceItem<Boolean>(
						LABEL_DEF_RED,
						DEF_DEF_RED, PreferenceType.Boolean),

				new UltimatePreferenceItem<Boolean>(
						LABEL_CHK_SAT,
						DEF_CHK_SAT, PreferenceType.Boolean),

				new UltimatePreferenceItem<Boolean>(
						LABEL_RM_FALSE,
						DEF_RM_FALSE, PreferenceType.Boolean),
		};
	}

	@Override
	protected String getPlugID() {
		return Activator.s_PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return "CodeCheck";
	}

	public enum SolverAndInterpolator {
		SMTINTERPOL, Z3SPWP
	}

	public enum EdgeCheckOptimization {
		NONE, PUSHPOP, SDEC, PUSHPOP_SDEC
	}

	public enum PredicateUnification {
		PER_ITERATION, PER_VERIFICATION, NONE
	}

	public enum Solver {
		Z3, SMTInterpol
	}
	
	public enum Checker {
		ULTIMATE, IMPULSE
	}
	
	public enum RedirectionStrategy {
		No_Strategy, FIRST, RANDOM, RANDOM_STRONGEST
	}


	/*
	 * labels for the different preferencess
	 */
//	public static final String LABEL_ONLYMAINPROCEDURE = "only verify starting from main procedure";
	
	public static final String LABEL_CHECKER = "the checking algorithm to use";
	
	public static final String LABEL_MEMOIZENORMALEDGECHECKS = "memoize already made edge checks for non-return edges";
	public static final String LABEL_MEMOIZERETURNEDGECHECKS = "memoize already made edge checks for return edges";

	public static final String LABEL_SOLVERANDINTERPOLATOR = "Interpolating solver";
	public static final String LABEL_INTERPOLATIONMODE = "tree interpolation mode for smtinterpol \n (internal: tree, a la matthias: nested)";
	public static final String LABEL_PREDICATEUNIFICATION = "Predicate Unification Mode";
	public static final String LABEL_EDGECHECKOPTIMIZATION = "EdgeCheck Optimization Mode";

	public static final String LABEL_GRAPHWRITERPATH = "write dot graph files here (empty for don't write)";

	public static final String LABEL_TIMEOUT = "Timeout in seconds";
	
	public static final String LABEL_ITERATIONS = "Limit maxmium number of iterations. (-1 for no limitations)";

	public static final String LABEL_REDIRECTION = "The redirection strategy for Impulse";
	
	public static final String LABEL_DEF_RED = "Default Redirection";
	
	public static final String LABEL_RM_FALSE = "Remove False Nodes Manually";
	
	public static final String LABEL_CHK_SAT = "Check edges satisfiability";
	// /*
	// * default values for the different preferences
	// */
	public static final Checker DEF_CHECKER = Checker.ULTIMATE;
	
	public static final boolean DEF_ONLYMAINPROCEDURE = false;
	public static final boolean DEF_MEMOIZENORMALEDGECHECKS = true;
	public static final boolean DEF_MEMOIZERETURNEDGECHECKS = true;

	public static final SolverAndInterpolator DEF_SOLVERANDINTERPOLATOR = SolverAndInterpolator.Z3SPWP;
	public static final INTERPOLATION DEF_INTERPOLATIONMODE = INTERPOLATION.Craig_TreeInterpolation;
	public static final PredicateUnification DEF_PREDICATEUNIFICATION = PredicateUnification.PER_ITERATION;
	public static final EdgeCheckOptimization DEF_EDGECHECKOPTIMIZATION = EdgeCheckOptimization.NONE;

	public static final String DEF_GRAPHWRITERPATH = "";

	public static final int DEF_TIMEOUT = 1000;
	
	public static final int DEF_ITERATIONS = -1;
	
	public static final RedirectionStrategy DEF_REDIRECTION = RedirectionStrategy.RANDOM_STRONGEST;
	
	public static final boolean DEF_DEF_RED = false;
	
	public static final boolean DEF_RM_FALSE = false;
	
	public static final boolean DEF_CHK_SAT = false;

}