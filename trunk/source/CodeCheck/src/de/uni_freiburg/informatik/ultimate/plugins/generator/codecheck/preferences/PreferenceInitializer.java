package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceInitializer.INTERPOLATION;

public class PreferenceInitializer extends UltimatePreferenceInitializer {

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<Boolean>(LABEL_ONLYMAINPROCEDURE,
						DEF_ONLYMAINPROCEDURE, PreferenceType.Boolean),
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

	/*
	 * labels for the different preferencess
	 */
	public static final String LABEL_ONLYMAINPROCEDURE = "only verify starting from main procedure";
	public static final String LABEL_MEMOIZENORMALEDGECHECKS = "memoize already made edge checks for non-return edges";
	public static final String LABEL_MEMOIZERETURNEDGECHECKS = "memoize already made edge checks for return edges";

	public static final String LABEL_SOLVERANDINTERPOLATOR = "Interpolating solver";
	public static final String LABEL_INTERPOLATIONMODE = "tree interpolation mode for smtinterpol \n (internal: tree, a la matthias: nested)";
	public static final String LABEL_PREDICATEUNIFICATION = "Predicate Unification Mode";
	public static final String LABEL_EDGECHECKOPTIMIZATION = "EdgeCheck Optimization Mode";

	public static final String LABEL_GRAPHWRITERPATH = "write dot graph files here (empty for don't write)";

	public static final String LABEL_TIMEOUT = "Timeout in seconds";

	// /*
	// * default values for the different preferences
	// */
	public static final boolean DEF_ONLYMAINPROCEDURE = false;
	public static final boolean DEF_MEMOIZENORMALEDGECHECKS = true;
	public static final boolean DEF_MEMOIZERETURNEDGECHECKS = true;

	public static final SolverAndInterpolator DEF_SOLVERANDINTERPOLATOR = SolverAndInterpolator.Z3SPWP;
	public static final INTERPOLATION DEF_INTERPOLATIONMODE = INTERPOLATION.Craig_TreeInterpolation;
	public static final PredicateUnification DEF_PREDICATEUNIFICATION = PredicateUnification.PER_ITERATION;
	public static final EdgeCheckOptimization DEF_EDGECHECKOPTIMIZATION = EdgeCheckOptimization.NONE;

	public static final String DEF_GRAPHWRITERPATH = "";

	public static final int DEF_TIMEOUT = 1000;

}