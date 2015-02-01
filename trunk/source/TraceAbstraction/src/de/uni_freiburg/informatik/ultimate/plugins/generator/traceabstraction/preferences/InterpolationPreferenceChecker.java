package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RCFGBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceInitializer.Solver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;

/**
 * Provides a method that checks compatibility of interpolation related
 * preferences.
 * 
 * @author Matthias Heizmann
 *
 */
public class InterpolationPreferenceChecker {
	
	public static void check (String pluginName, INTERPOLATION interpolation) {
		Solver solver = (new UltimatePreferenceStore(RCFGBuilder.s_PLUGIN_ID))
				.getEnum(PreferenceInitializer.LABEL_Solver, Solver.class);
		Set<Solver> legalSolverSettings = new HashSet<Solver>();
		switch (interpolation) {
		case Craig_TreeInterpolation:
			legalSolverSettings.add(Solver.Internal_SMTInterpol);
			break;
		case Craig_NestedInterpolation:
			legalSolverSettings.add(Solver.Internal_SMTInterpol);
			legalSolverSettings.add(Solver.External_PrincessInterpolationMode);
			legalSolverSettings.add(Solver.External_Z3InterpolationMode);
			break;
		case BackwardPredicates:
		case FPandBP:
		case ForwardPredicates:
		case PathInvariants:
			legalSolverSettings.add(Solver.Internal_SMTInterpol);
			legalSolverSettings.add(Solver.External_Z3InterpolationMode);
			break;
		default:
			throw new AssertionError("unknown option " + interpolation);
		}
		if (!legalSolverSettings.contains(solver)) {
			String errorMessage = "Incompatible preferences. You want to use " 
				+ interpolation + " in the " + pluginName + 
				" plugin. This requires that " + 
				PreferenceInitializer.LABEL_Solver + 
				" in the " + RCFGBuilder.s_PLUGIN_ID + 
				" has one of the following values. " +
				legalSolverSettings.toString();
			throw new UnsupportedOperationException(errorMessage);
		}
	}

}
